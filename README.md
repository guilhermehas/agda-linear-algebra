# Linear Algebra in Agda

A library for doing linear algebra in Agda. With this library, it is possible to normalize a matrix using Gauss Elimination.
See this [file example](https://github.com/guilhermehas/agda-linear-algebra/blob/master/src/Examples/NormRational.agda).
There are also some proofs that the normalization algorithm works.
Look also at the [API example](https://github.com/guilhermehas/agda-linear-algebra/blob/master/src/Examples/API.agda) to see how the main data types are used in this project.

## Usage
Clone the repository and inside the project directory run these commands:

### Nix
Get the nix environment:

``` sh
nix develop
```

### Agda
Compile agda files:

``` sh
agda src/EverythingUseful.agda
```

## Documentation
+ See [Typst website](https://typst.app) to understand how Typst works.
+ It is not possible to compile Typst documents using Nix, but if you have Typst installed in your machine, you can run to visualize the documentation:

``` sh
typst compile main.typ
```

