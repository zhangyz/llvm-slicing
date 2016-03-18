# llvm-slicing: Symbolic Program Slicing with LLVM

## Motivation    

Program slicing is a technique for simplifying programs by focusing on selected aspects of their behaviour. Current slicing techniques still have much room for improvement, such as handling programs written in multiple languages. Using the modern compilation framework [LLVM](http://llvm.org) (Low-Level Virtual Machine), we attempt in this project to meet this improvement by presenting a language-independent context-sensitive slicing approach, called `Symbolic Program Slicing`, including both backward and forward static slicing. In the symbolic slicing approach, slices are stored symbolically rather than procedure being re-analysed (cf. procedure summaries). For comparison, we systematically adapt SDG-based slicing methods with IFDS (Interprocedural Finite Distributive Subset analysis) to statically slice LLVM IR (intermediate representation). 

## Installation

`llvm-slicing` is written in [Haskell](https://www.haskell.org/). It depends on `LLVM 3.0-3.4` and `llvm-config` must be in your `PATH`. It is built and packaged using [`Cabal`](https://www.haskell.org/cabal/). 
 - Install the package `cabal-install` from your system's package manager (with e.g. `apt-get`); <br>
   Verify that `cabal` is installed and update its dependency list with  `cabal update`
 - `git clone` this repository, and `cd` to the `llvm-slicing` source directory (`src`) to build/install: `cabal install`. <br>
   This will compile `llvm-slicing` and install it to your `~/.cabal/bin` directory
 - Add this directory to your `PATH`; <br> Verify that your `PATH` is set up correctly with `which llvm-slicing`

Alternatively, download our pre-built binary for Ubuntu 12.04 LTS (64 bit) with LLVM 3.3: <br> 
     [`llvm-slicing_llvm-3.3_x86-64_Ubuntu-12.04.2.tar.bz2`](bin/llvm-slicing_llvm-3.3_x86-64_Ubuntu-12.04.2.tar.bz2)  <br>
Then unzip it and put the binary `llvm-slicing` in a directory that is on your `PATH`

## Usage

Currently, `llvm-slicing` includes four static slicers based on corresponding slicing methods, i.e. Symbolic slicing, Weiser slicing, SDG-based slicing (using intraprocedure slice result to generate summary edges), and IFDS-based slicing (using IFDS method to generate summary edges). To get detail help infomation:   

     $ llvm-slicing -h
    
       llvm-slicing [-c|--criterion VARIABLES] [-d|--direction DIRECTION]
                    [-m|--method SLICE_METHOD] [-p|--isParallel ISPARALLEL]
                    [-t|--timeout TIMEOUT] [-g|--graph GRAPH_SHOW]
                    [-o|--output FILE/DIR] FILE
 
       Available options:
         -h,--help                  Show this help text
         -c,--criterion VARIABLES   The criterion variables (with the form of Var@Fun,e.g. x@main) for slicing. 
                                    If null, just output the slice table for all single variables.
         -d,--direction DIRECTION   The type of output to slice: Fwd, Bwd or Both. Default: Bwd
         -m,--method SLICE_METHOD   The slice algorithm: Symbolic,Weiser,SDG or IFDS. Default: Symbolic
         -p,--isParallel ISPARALLEL Whether or not travelling SCC in callgraph in parallel. Default: False
         -t,--timeout TIMEOUT       The timeout (sec.) for running slicer. Default: 1800
         -g,--graph GRAPH_SHOW      Print related graphs: Sdg,Cg,Cdg,Cfg,Icfg,Pdt or Dt.
         -o,--output FILE/DIR       The destination of a file output
         FILE                       The input file which can be bitcode,llvm assembly, or C/CPP sourcecode

For a multi-programs library, it must be converted to LLVM bitcode (e.g. using the [whole-program LLVM](https://github.com/travitch/whole-program-llvm) wrapper to compile the library) before using `llvm-slicing` to slice it.

For a simple C example program and its slice results with some graphs such as SDG, CG, CFG, please visit the folder [`test/C/sample`](test/C/sample/).   
