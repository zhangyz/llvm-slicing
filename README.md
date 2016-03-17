# llvm-slicing: Symbolic Program Slicing with LLVM
## Motivation    
Program slicing is a technique for simplifying programs by focusing on selected aspects of their behaviour. Current slicing techniques still have much room for improvement, such as handling programs written in multiple languages. Using the modern compilation framework [LLVM](http://llvm.org) (Low-Level Virtual Machine), we attempt in this project to meet this improvement by presenting a language-independent context-sensitive slicing approach, called `Symbolic Program Slicing`, including both backward and forward static slicing. In the symbolic slicing approach, slices are stored symbolically rather than procedure being re-analysed (cf. procedure summaries). For comparison, we systematically adapt SDG-based slicing methods with IFDS to statically slice LLVM IR (intermediate representation). 

## Installation
`llvm-slicing` is written in [Haskell](https://www.haskell.org/). It depends on `LLVM 3.0-3.3` and `llvm-config` must be in your `PATH`. It is built and packaged using [`Cabal`](https://www.haskell.org/cabal/). 
 - Install the package `cabal-install` from your system's package manager (with e.g. `apt-get`); <br>
   Verify that `cabal` is installed and update its dependency list with  `cabal update`
 - `git clone` this repository, and `cd` to the `llvm-slicing` source directory (`src`) to build/install: `cabal install`. <br>
   This will compile `llvm-slicing` and install it to your `~/.cabal/bin` directory
 - Add this directory to your `PATH`; <br> Verify that your `PATH` is set up correctly with `which llvm-slicing`

