// Copyright 2012 the V8 project authors. All rights reserved.
//
// Copyright IBM Corp. 2012, 2013. All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above
//       copyright notice, this list of conditions and the following
//       disclaimer in the documentation and/or other materials provided
//       with the distribution.
//     * Neither the name of Google Inc. nor the names of its
//       contributors may be used to endorse or promote products derived
//       from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "v8.h"

#if defined(V8_TARGET_ARCH_PPC)

#include "codegen.h"
#include "macro-assembler.h"
#include "simulator-ppc.h"

namespace v8 {
namespace internal {


UnaryMathFunction CreateTranscendentalFunction(TranscendentalCache::Type type) {
  switch (type) {
    case TranscendentalCache::SIN: return &sin;
    case TranscendentalCache::COS: return &cos;
    case TranscendentalCache::TAN: return &tan;
    case TranscendentalCache::LOG: return &log;
    default: UNIMPLEMENTED();
  }
  return NULL;
}


#define __ masm.


#if defined(USE_SIMULATOR)
byte* fast_exp_arm_machine_code = NULL;
double fast_exp_simulator(double x) {
  return Simulator::current(Isolate::Current())->CallFP(
      fast_exp_arm_machine_code, x, 0);
}
#endif


UnaryMathFunction CreateExpFunction() {
  if (!FLAG_fast_math) return &exp;
  size_t actual_size;
  byte* buffer = static_cast<byte*>(OS::Allocate(1 * KB, &actual_size, true));
  if (buffer == NULL) return &exp;
  ExternalReference::InitializeMathExpData();

  MacroAssembler masm(NULL, buffer, static_cast<int>(actual_size));

  {
    DwVfpRegister input = d0;
    DwVfpRegister result = d1;
    DwVfpRegister double_scratch1 = d2;
    DwVfpRegister double_scratch2 = d3;
    Register temp1 = r4;
    Register temp2 = r5;
    Register temp3 = r6;

    if (masm.use_eabi_hardfloat()) {
      // Input value is in d0 anyway, nothing to do.
    } else {
      __ vmov(input, r0, r1);
    }
    __ Push(temp3, temp2, temp1);
    MathExpGenerator::EmitMathExp(
        &masm, input, result, double_scratch1, double_scratch2,
        temp1, temp2, temp3);
    __ Pop(temp3, temp2, temp1);
    if (masm.use_eabi_hardfloat()) {
      __ vmov(d0, result);
    } else {
      __ vmov(r0, r1, result);
    }
    __ Ret();
  }

  CodeDesc desc;
  masm.GetCode(&desc);
  ASSERT(!RelocInfo::RequiresRelocation(desc));

  CPU::FlushICache(buffer, actual_size);
  OS::ProtectCode(buffer, actual_size);

#if !defined(USE_SIMULATOR)
  return FUNCTION_CAST<UnaryMathFunction>(buffer);
#else
  fast_exp_arm_machine_code = buffer;
  return &fast_exp_simulator;
#endif
}


#undef __


UnaryMathFunction CreateSqrtFunction() {
  return &sqrt;
}

// -------------------------------------------------------------------------
// Platform-specific RuntimeCallHelper functions.

void StubRuntimeCallHelper::BeforeCall(MacroAssembler* masm) const {
  masm->EnterFrame(StackFrame::INTERNAL);
  ASSERT(!masm->has_frame());
  masm->set_has_frame(true);
}


void StubRuntimeCallHelper::AfterCall(MacroAssembler* masm) const {
  masm->LeaveFrame(StackFrame::INTERNAL);
  ASSERT(masm->has_frame());
  masm->set_has_frame(false);
}


// -------------------------------------------------------------------------
// Code generators

#define __ ACCESS_MASM(masm)

void ElementsTransitionGenerator::GenerateMapChangeElementsTransition(
    MacroAssembler* masm, AllocationSiteMode mode,
    Label* allocation_site_info_found) {
  // ----------- S t a t e -------------
  //  -- r3    : value
  //  -- r4    : key
  //  -- r5    : receiver
  //  -- lr    : return address
  //  -- r6    : target map, scratch for subsequent call
  //  -- r7    : scratch (elements)
  // -----------------------------------
  if (mode == TRACK_ALLOCATION_SITE) {
    ASSERT(allocation_site_info_found != NULL);
    __ TestJSArrayForAllocationSiteInfo(r5, r7);
    __ b(eq, allocation_site_info_found);
  }

  // Set transitioned map.
  __ stw(r6, FieldMemOperand(r5, HeapObject::kMapOffset));
  __ RecordWriteField(r5,
                      HeapObject::kMapOffset,
                      r6,
                      r22,
                      kLRHasNotBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
}


void ElementsTransitionGenerator::GenerateSmiToDouble(
    MacroAssembler* masm, AllocationSiteMode mode, Label* fail) {
  // ----------- S t a t e -------------
  //  -- r3    : value
  //  -- r4    : key
  //  -- r5    : receiver
  //  -- lr    : return address
  //  -- r6    : target map, scratch for subsequent call
  //  -- r7    : scratch (elements)
  // -----------------------------------
  Label loop, entry, convert_hole, gc_required, only_change_map, done;

  if (mode == TRACK_ALLOCATION_SITE) {
    __ TestJSArrayForAllocationSiteInfo(r5, r7);
    __ b(eq, fail);
  }

  // Check for empty arrays, which only require a map transition and no changes
  // to the backing store.
  __ lwz(r7, FieldMemOperand(r5, JSObject::kElementsOffset));
  __ CompareRoot(r7, Heap::kEmptyFixedArrayRootIndex);
  __ beq(&only_change_map);

  __ push(lr);
  __ lwz(r8, FieldMemOperand(r7, FixedArray::kLengthOffset));
  // r7: source FixedArray
  // r8: number of elements (smi-tagged)

  // Allocate new FixedDoubleArray.
  // Use lr as a temporary register.
  __ slwi(lr, r8, Operand(2));
  __ add(lr, lr, Operand(FixedDoubleArray::kHeaderSize + kPointerSize));
  __ Allocate(lr, r9, r10, r22, &gc_required, DOUBLE_ALIGNMENT);
  // r9: destination FixedDoubleArray, not tagged as heap object.

  // Set destination FixedDoubleArray's length and map.
  __ LoadRoot(r22, Heap::kFixedDoubleArrayMapRootIndex);
  __ stw(r8, MemOperand(r9, FixedDoubleArray::kLengthOffset));
  // Update receiver's map.
  __ stw(r22, MemOperand(r9, HeapObject::kMapOffset));

  __ stw(r6, FieldMemOperand(r5, HeapObject::kMapOffset));
  __ RecordWriteField(r5,
                      HeapObject::kMapOffset,
                      r6,
                      r22,
                      kLRHasBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
  // Replace receiver's backing store with newly created FixedDoubleArray.
  __ add(r6, r9, Operand(kHeapObjectTag));
  __ stw(r6, FieldMemOperand(r5, JSObject::kElementsOffset));
  __ RecordWriteField(r5,
                      JSObject::kElementsOffset,
                      r6,
                      r22,
                      kLRHasBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);

  // Prepare for conversion loop.
  __ add(r6, r7, Operand(FixedArray::kHeaderSize - kHeapObjectTag));
  __ add(r10, r9, Operand(FixedDoubleArray::kHeaderSize));
  __ slwi(r9, r8, Operand(2));
  __ add(r9, r10, r9);
  __ mov(r7, Operand(kHoleNanLower32));
  __ mov(r8, Operand(kHoleNanUpper32));
  // r6: begin of source FixedArray element fields, not tagged
  // r7: kHoleNanLower32
  // r8: kHoleNanUpper32
  // r9: end of destination FixedDoubleArray, not tagged
  // r10: begin of FixedDoubleArray element fields, not tagged
  __ b(&entry);

  __ bind(&only_change_map);
  __ stw(r6, FieldMemOperand(r5, HeapObject::kMapOffset));
  __ RecordWriteField(r5,
                      HeapObject::kMapOffset,
                      r6,
                      r22,
                      kLRHasNotBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
  __ b(&done);

  // Call into runtime if GC is required.
  __ bind(&gc_required);
  __ pop(lr);
  __ b(fail);

  // Convert and copy elements.
  __ bind(&loop);
  __ lwz(r22, MemOperand(r6, 4, PostIndex));
  // r22: current element
  __ UntagAndJumpIfNotSmi(r22, r22, &convert_hole);

  // Normal smi, convert to double and store.
  FloatingPointHelper::ConvertIntToDouble(
    masm, r22, FloatingPointHelper::kFPRegisters,
    d0, r7, r7,  // r7 unused as we're using kFPRegisters
    d2);
  __ stfd(d0, r10, 0);
  __ add(r10, r10, Operand(8));

  __ b(&entry);

  // Hole found, store the-hole NaN.
  __ bind(&convert_hole);
  if (FLAG_debug_code) {
    // Restore a "smi-untagged" heap object.
    __ SmiTag(r22);
    __ ori(r22, r22, Operand(1));
    __ CompareRoot(r22, Heap::kTheHoleValueRootIndex);
    __ Assert(eq, "object found in smi-only array");
  }
  __ stw(r7, MemOperand(r10, 0));
  __ stw(r8, MemOperand(r10, 4));
  __ add(r10, r10, Operand(8));

  __ bind(&entry);
  __ cmp(r10, r9);
  __ blt(&loop);

  __ pop(lr);
  __ bind(&done);
}


void ElementsTransitionGenerator::GenerateDoubleToObject(
    MacroAssembler* masm, AllocationSiteMode mode, Label* fail) {
  // ----------- S t a t e -------------
  //  -- r3    : value
  //  -- r4    : key
  //  -- r5    : receiver
  //  -- lr    : return address
  //  -- r6    : target map, scratch for subsequent call
  //  -- r7    : scratch (elements)
  // -----------------------------------
  // we also use ip as a scratch register
  Label entry, loop, convert_hole, gc_required, only_change_map;

  if (mode == TRACK_ALLOCATION_SITE) {
    __ TestJSArrayForAllocationSiteInfo(r5, r7);
    __ b(eq, fail);
  }

  // Check for empty arrays, which only require a map transition and no changes
  // to the backing store.
  __ lwz(r7, FieldMemOperand(r5, JSObject::kElementsOffset));
  __ CompareRoot(r7, Heap::kEmptyFixedArrayRootIndex);
  __ beq(&only_change_map);

  __ Push(r6, r5, r4, r3);
  __ lwz(r8, FieldMemOperand(r7, FixedArray::kLengthOffset));
  // r7: source FixedDoubleArray
  // r8: number of elements (smi-tagged)

  // Allocate new FixedArray.
  __ li(r3, Operand(FixedDoubleArray::kHeaderSize));
  __ slwi(ip, r8, Operand(1));
  __ add(r3, r3, ip);
  __ Allocate(r3, r9, r10, r22, &gc_required, NO_ALLOCATION_FLAGS);
  // r9: destination FixedArray, not tagged as heap object
  // Set destination FixedDoubleArray's length and map.
  __ LoadRoot(r22, Heap::kFixedArrayMapRootIndex);
  __ stw(r8, MemOperand(r9, FixedDoubleArray::kLengthOffset));
  __ stw(r22, MemOperand(r9, HeapObject::kMapOffset));

  // Prepare for conversion loop.
  __ add(r7, r7, Operand(FixedDoubleArray::kHeaderSize - kHeapObjectTag + 4));
  __ add(r6, r9, Operand(FixedArray::kHeaderSize));
  __ add(r9, r9, Operand(kHeapObjectTag));
  __ slwi(r8, r8, Operand(1));
  __ add(r8, r6, r8);
  __ LoadRoot(r10, Heap::kTheHoleValueRootIndex);
  __ LoadRoot(r22, Heap::kHeapNumberMapRootIndex);
  // Using offsetted addresses in r7 to fully take advantage of post-indexing.
  // r6: begin of destination FixedArray element fields, not tagged
  // r7: begin of source FixedDoubleArray element fields, not tagged, +4
  // r8: end of destination FixedArray, not tagged
  // r9: destination FixedArray
  // r10: the-hole pointer
  // r22: heap number map
  __ b(&entry);

  // Call into runtime if GC is required.
  __ bind(&gc_required);
  __ Pop(r6, r5, r4, r3);
  __ b(fail);

  __ bind(&loop);
  __ lwz(r4, MemOperand(r7));
  __ add(r7, r7, Operand(8));
  // ip: current element's upper 32 bit
  // r7: address of next element's upper 32 bit
  __ mov(r0, Operand(kHoleNanUpper32));
  __ cmp(r4, r0);
  __ beq(&convert_hole);

  // Non-hole double, copy value into a heap number.
  __ push(r4);
  __ mr(r4, ip);
  __ AllocateHeapNumber(r5, r3, r4, r22, &gc_required);
  __ mr(ip, r4);
  __ pop(r4);
  // r5: new heap number
  __ lwz(r3, MemOperand(r7, -12));
  __ stw(r3, FieldMemOperand(r5, HeapNumber::kValueOffset));
  __ stw(r4, FieldMemOperand(r5, HeapNumber::kValueOffset+4));
  __ mr(r3, r6);
  __ stw(r5, MemOperand(r6));
  __ add(r6, r6, Operand(4));
  __ RecordWrite(r9,
                 r3,
                 r5,
                 kLRHasBeenSaved,
                 kDontSaveFPRegs,
                 EMIT_REMEMBERED_SET,
                 OMIT_SMI_CHECK);
  __ b(&entry);

  // Replace the-hole NaN with the-hole pointer.
  __ bind(&convert_hole);
  __ stw(r10, MemOperand(r6));
  __ add(r6, r6, Operand(4));

  __ bind(&entry);
  __ cmpl(r6, r8);
  __ blt(&loop);

  __ Pop(r6, r5, r4, r3);
  // Replace receiver's backing store with newly created and filled FixedArray.
  __ stw(r9, FieldMemOperand(r5, JSObject::kElementsOffset));
  __ RecordWriteField(r5,
                      JSObject::kElementsOffset,
                      r9,
                      r22,
                      kLRHasBeenSaved,
                      kDontSaveFPRegs,
                      EMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);

  __ bind(&only_change_map);
  // Update receiver's map.
  __ stw(r6, FieldMemOperand(r5, HeapObject::kMapOffset));
  __ RecordWriteField(r5,
                      HeapObject::kMapOffset,
                      r6,
                      r22,
                      kLRHasNotBeenSaved,
                      kDontSaveFPRegs,
                      OMIT_REMEMBERED_SET,
                      OMIT_SMI_CHECK);
}


// roohack - assume ip can be used as a scratch register below
void StringCharLoadGenerator::Generate(MacroAssembler* masm,
                                       Register string,
                                       Register index,
                                       Register result,
                                       Label* call_runtime) {
  // Fetch the instance type of the receiver into result register.
  __ lwz(result, FieldMemOperand(string, HeapObject::kMapOffset));
  __ lbz(result, FieldMemOperand(result, Map::kInstanceTypeOffset));

  // We need special handling for indirect strings.
  Label check_sequential;
  __ andi(r0, result, Operand(kIsIndirectStringMask));
  __ cmpi(r0, Operand(0));
  __ beq(&check_sequential);

  // Dispatch on the indirect string shape: slice or cons.
  Label cons_string;
  __ mov(ip, Operand(kSlicedNotConsMask));
  __ and_(r0, result, ip, LeaveRC);
  __ cmpi(r0, Operand(0));
  __ beq(&cons_string);

  // Handle slices.
  Label indirect_string_loaded;
  __ lwz(result, FieldMemOperand(string, SlicedString::kOffsetOffset));
  __ lwz(string, FieldMemOperand(string, SlicedString::kParentOffset));
  __ srawi(ip, result, kSmiTagSize);
  __ add(index, index, ip);
  __ jmp(&indirect_string_loaded);

  // Handle cons strings.
  // Check whether the right hand side is the empty string (i.e. if
  // this is really a flat string in a cons string). If that is not
  // the case we would rather go to the runtime system now to flatten
  // the string.
  __ bind(&cons_string);
  __ lwz(result, FieldMemOperand(string, ConsString::kSecondOffset));
  __ CompareRoot(result, Heap::kempty_stringRootIndex);
  __ bne(call_runtime);
  // Get the first of the two strings and load its instance type.
  __ lwz(string, FieldMemOperand(string, ConsString::kFirstOffset));

  __ bind(&indirect_string_loaded);
  __ lwz(result, FieldMemOperand(string, HeapObject::kMapOffset));
  __ lbz(result, FieldMemOperand(result, Map::kInstanceTypeOffset));

  // Distinguish sequential and external strings. Only these two string
  // representations can reach here (slices and flat cons strings have been
  // reduced to the underlying sequential or external string).
  Label external_string, check_encoding;
  __ bind(&check_sequential);
  STATIC_ASSERT(kSeqStringTag == 0);
  __ andi(r0, result, Operand(kStringRepresentationMask));
  __ cmpi(r0, Operand(0));
  __ bne(&external_string);

  // Prepare sequential strings
  STATIC_ASSERT(SeqTwoByteString::kHeaderSize == SeqOneByteString::kHeaderSize);
  __ add(string,
         string,
         Operand(SeqTwoByteString::kHeaderSize - kHeapObjectTag));
  __ jmp(&check_encoding);

  // Handle external strings.
  __ bind(&external_string);
  if (FLAG_debug_code) {
    // Assert that we do not have a cons or slice (indirect strings) here.
    // Sequential strings have already been ruled out.
    __ andi(r0, result, Operand(kIsIndirectStringMask));
    __ cmpi(r0, Operand(0));
    __ Assert(eq, "external string expected, but not found");
  }
  // Rule out short external strings.
  STATIC_CHECK(kShortExternalStringTag != 0);
  __ andi(r0, result, Operand(kShortExternalStringMask));
  __ cmpi(r0, Operand(0));
  __ bne(call_runtime);
  __ lwz(string, FieldMemOperand(string, ExternalString::kResourceDataOffset));

  Label ascii, done;
  __ bind(&check_encoding);
  STATIC_ASSERT(kTwoByteStringTag == 0);
  __ andi(r0, result, Operand(kStringEncodingMask));
  __ cmpi(r0, Operand(0));
  __ bne(&ascii);
  // Two-byte string.
  __ slwi(result, index, Operand(1));
  __ add(result, result, string);
  __ lhz(result, MemOperand(result));
  __ jmp(&done);
  __ bind(&ascii);
  // Ascii string.
  __ add(result, string, index);
  __ lbz(result, MemOperand(result));
  __ bind(&done);
}

static MemOperand ExpConstant(int index, Register base) {
  return MemOperand(base, index * kDoubleSize);
}


void MathExpGenerator::EmitMathExp(MacroAssembler* masm,
                                   DwVfpRegister input,
                                   DwVfpRegister result,
                                   DwVfpRegister double_scratch1,
                                   DwVfpRegister double_scratch2,
                                   Register temp1,
                                   Register temp2,
                                   Register temp3) {
  ASSERT(!input.is(result));
  ASSERT(!input.is(double_scratch1));
  ASSERT(!input.is(double_scratch2));
  ASSERT(!result.is(double_scratch1));
  ASSERT(!result.is(double_scratch2));
  ASSERT(!double_scratch1.is(double_scratch2));
  ASSERT(!temp1.is(temp2));
  ASSERT(!temp1.is(temp3));
  ASSERT(!temp2.is(temp3));
  ASSERT(ExternalReference::math_exp_constants(0).address() != NULL);

  Label done;

  __ mov(temp3, Operand(ExternalReference::math_exp_constants(0)));

  __ vldr(double_scratch1, ExpConstant(0, temp3));
  __ vmov(result, kDoubleRegZero);
  __ VFPCompareAndSetFlags(double_scratch1, input);
  __ b(ge, &done);
  __ vldr(double_scratch2, ExpConstant(1, temp3));
  __ VFPCompareAndSetFlags(input, double_scratch2);
  __ vldr(result, ExpConstant(2, temp3));
  __ b(ge, &done);
  __ vldr(double_scratch1, ExpConstant(3, temp3));
  __ vldr(result, ExpConstant(4, temp3));
  __ vmul(double_scratch1, double_scratch1, input);
  __ vadd(double_scratch1, double_scratch1, result);
  __ vmov(temp2, temp1, double_scratch1);
  __ vsub(double_scratch1, double_scratch1, result);
  __ vldr(result, ExpConstant(6, temp3));
  __ vldr(double_scratch2, ExpConstant(5, temp3));
  __ vmul(double_scratch1, double_scratch1, double_scratch2);
  __ vsub(double_scratch1, double_scratch1, input);
  __ vsub(result, result, double_scratch1);
  __ vmul(input, double_scratch1, double_scratch1);
  __ vmul(result, result, input);
  __ mov(temp1, Operand(temp2, LSR, 11));
  __ vldr(double_scratch2, ExpConstant(7, temp3));
  __ vmul(result, result, double_scratch2);
  __ vsub(result, result, double_scratch1);
  __ vldr(double_scratch2, ExpConstant(8, temp3));
  __ vadd(result, result, double_scratch2);
// roohack  __ movw(ip, 0x7ff);
  __ and_(temp2, temp2, Operand(ip));
  __ add(temp1, temp1, Operand(0x3ff));
  __ mov(temp1, Operand(temp1, LSL, 20));

  // Must not call ExpConstant() after overwriting temp3!
  __ mov(temp3, Operand(ExternalReference::math_exp_log_table()));
  __ ldr(ip, MemOperand(temp3, temp2, LSL, 3));
  __ add(temp3, temp3, Operand(kPointerSize));
  __ ldr(temp2, MemOperand(temp3, temp2, LSL, 3));
  __ orr(temp1, temp1, temp2);
  __ vmov(input, ip, temp1);
  __ vmul(result, result, input);
  __ bind(&done);
}

#undef __

// add(r0, pc, Operand(-8))
static const uint32_t kCodeAgePatchFirstInstruction = 0xe24f0008;

static byte* GetNoCodeAgeSequence(uint32_t* length) {
  // The sequence of instructions that is patched out for aging code is the
  // following boilerplate stack-building prologue that is found in FUNCTIONS
  static bool initialized = false;
  static uint32_t sequence[kNoCodeAgeSequenceLength];
  byte* byte_sequence = reinterpret_cast<byte*>(sequence);
  *length = kNoCodeAgeSequenceLength * Assembler::kInstrSize;
  if (!initialized) {
    CodePatcher patcher(byte_sequence, kNoCodeAgeSequenceLength);
    PredictableCodeSizeScope scope(patcher.masm(), *length);
#if 0
    patcher.masm()->stm(db_w, sp, r1.bit() | cp.bit() | fp.bit() | lr.bit());
    patcher.masm()->LoadRoot(ip, Heap::kUndefinedValueRootIndex);
    patcher.masm()->add(fp, sp, Operand(2 * kPointerSize));
#else
    patcher.masm()->fake_asm(fMASM46);
#endif
    initialized = true;
  }
  return byte_sequence;
}


bool Code::IsYoungSequence(byte* sequence) {
  uint32_t young_length;
  byte* young_sequence = GetNoCodeAgeSequence(&young_length);
  bool result = !memcmp(sequence, young_sequence, young_length);
  ASSERT(result ||
         Memory::uint32_at(sequence) == kCodeAgePatchFirstInstruction);
  return result;
}


void Code::GetCodeAgeAndParity(byte* sequence, Age* age,
                               MarkingParity* parity) {
  if (IsYoungSequence(sequence)) {
    *age = kNoAge;
    *parity = NO_MARKING_PARITY;
  } else {
    Address target_address = Memory::Address_at(
        sequence + Assembler::kInstrSize * (kNoCodeAgeSequenceLength - 1));
    Code* stub = GetCodeFromTargetAddress(target_address);
    GetCodeAgeAndParity(stub, age, parity);
  }
}

void Code::PatchPlatformCodeAge(byte* sequence,
                                Code::Age age,
                                MarkingParity parity) {
  uint32_t young_length;
  byte* young_sequence = GetNoCodeAgeSequence(&young_length);
  if (age == kNoAge) {
    CopyBytes(sequence, young_sequence, young_length);
    CPU::FlushICache(sequence, young_length);
  } else {
#if 0
    Code* stub = GetCodeAgeStub(age, parity);
    CodePatcher patcher(sequence, young_length / Assembler::kInstrSize);
    patcher.masm()->add(r0, pc, Operand(-8));
    patcher.masm()->ldr(pc, MemOperand(pc, -4));
    patcher.masm()->dd(reinterpret_cast<uint32_t>(stub->instruction_start()));
#else
    CodePatcher patcher(sequence, young_length / Assembler::kInstrSize);
    patcher.masm()->fake_asm(fMASM47);
#endif
  }
}

} }  // namespace v8::internal

#endif  // V8_TARGET_ARCH_PPC
