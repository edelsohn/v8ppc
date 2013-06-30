v8ppc
=====

Port of Google V8 javascript engine to PowerPC - PowerLinux and AIX.

June 11th 88% of the tests were passing. 

Compile code:<br><code>
make dependencies; make -j8 ppc snapshot=off regexp=interpreted
</code>

Test code:<br><code>
tools/run-tests.py -j 24 --progress=dots --no-presubmit --arch-and-mode=ppc.debug --junitout v8tests-junit.xml
</code>
