# Name of the executable as declared in your dune file (the `name` field)
EXE      := main
# Path to the executable's dune directory, relative to the project root
EXE_DIR  := bin
TEST_DIR := test
TEST_EXE := test_fictol
UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer -z noexecstack
endif
.PHONY: _build test

build:
	dune build

test:
	dune build


test/output/%.run: test/output/%.o driver.c 
	clang $(CLANG_FLAGS) -o $@ driver.c $<

test/output/%.o: test/output/%.ll
	llc -filetype=obj  -o $@ $<

.PRECIOUS: test/output/%.ll
test/output/%.ll: test/input/%.fic main
	./main $< > $@

test/output/do_pass/%.run: test/output/do_pass/%.o driver.c
	clang $(CLANG_FLAGS) -o $@  driver.c $<

test/output/do_pass/%.o: test/output/do_pass/%.ll
	llc -filetype=obj -o $@ $<

.PRECIOUS: test/output/do_pass/%.ll
test/output/do_pass/%.ll: test/input/do_pass/%.fic main
	./main $< > $@


test/output/dont_pass/%.run: test/output/dont_pass/%.o driver.c 
	clang -g $(CLANG_FLAGS) -o $@  driver.c $<

test/output/dont_pass/%.o: test/output/dont_pass/%.ll
	llc -filetype=obj  -o $@ $<

.PRECIOUS: test/output/dont_pass/%.ll
test/output/dont_pass/%.ll: test/input/dont_pass/%.fic main
	./main $< > $@


test/output/do_err/%.run: test/output/do_err/%.o driver.c 
	clang $(CLANG_FLAGS) -o $@  driver.c $<

test/output/do_err/%.o: test/output/do_err/%.ll
	llc -filetype=obj  -o $@ $<

.PRECIOUS: test/output/do_err/%.ll
test/output/do_err/%.ll: test/input/do_err/%.fic main
	./main $< > $@


test/output/dont_err/%.run: test/output/dont_err/%.o driver.c 
	clang -g $(CLANG_FLAGS) -o $@  driver.c $<

test/output/dont_err/%.o: test/output/dont_err/%.ll
	llc -filetype=obj  -o $@ $<

.PRECIOUS: test/output/dont_err/%.ll
test/output/dont_err/%.ll: test/input/dont_err/%.fic main
	./main $< > $@

clean:
	dune clean
	rm -rf test/output/*.o test/output/*.ll test/output/*.dSYM test/output/*.run *.log *.o
	rm -rf test/output/*/*.o test/output/*/*.ll test/output/*/*.dSYM test/output/*/*.run
	rm -rf fun/*.o