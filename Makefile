# Name of the executable as declared in your dune file (the `name` field)
EXE      := main
# Path to the executable's dune directory, relative to the project root
EXE_DIR  := bin

.PHONY: all clean

all:
	dune build
	ln -sf _build/default/$(EXE_DIR)/$(EXE).exe ./$(EXE)

clean:
	dune clean
	rm -f ./$(EXE)