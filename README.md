# SDC (SMT Dafny Compiler) [![Docker Image CI](https://github.com/m-carrasco/smt-dafny-compiler/actions/workflows/docker-image.yml/badge.svg)](https://github.com/m-carrasco/smt-dafny-compiler/actions/workflows/docker-image.yml)

SDC compiles an SMT formula into a Dafny program. The synthesized program can then be verified to reveal bugs in Dafny.

## Toy Example: SMT Pointwise Test 

The following example shows how SDC synthesizes a Dafny program `P` for an SMT formula `F`. In addition, `F` is optimized using SLOT into `F'`. Then, Dafny must prove that `F` is equivalent to `F'`. If the program cannot be proven safe, the test found a bug in Dafny.

### Input Formula `F`

```
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (bvlshr x #b00001000) (bvlshr y #b00000001))) 
(check-sat)
```

### Equivalent Formula `F'`

```
(declare-fun y () (_ BitVec 8))
(assert
 (bvult y (_ bv2 8)))
(check-sat)
```

### Dafny Program `P`

The verifier is then tasked with proving the following program correct. This program also has a harness that allows it to be executed concretely. 

```
function Spec(x : bv8, y : bv8) : bool
{
    (y < (2 as bv8))
}

method  Constraints(x : bv8, y : bv8) returns (sat : bool)
    ensures (Spec(x, y) == sat)
{
    var l0 : bv8;
    var l1 : bv8;
    var l2 : bv8;
    var l3 : bv8;
    var l4 : bv8;
    var l5 : bv8;
    var l6 : bool;
    
    l0 := x;
    l1 := (8 as bv8);
    l2 := ((l0 as bv8) >> l1);
    l3 := y;
    l4 := (1 as bv8);
    l5 := ((l3 as bv8) >> l4);
    l6 := (l2 == l5);
    if ((l6 == false)) {
        return false;
    }
    return true;
}
```

## Requirements

1. Docker
2. .NET SDK 8.0


## Visual Studio Code: Dev Container 

In this way, Visual Studio Code runs inside a container. The project is configured so that changes to the repository in the container are reflected outside.

1. Build the required Docker images: ```./ci/build-images.sh```.
2. In Visual Studio Code, click `> Dev Containers: Rebuild and Reopen in Container`.
3. Open a terminal in Visual Studio Code, now mapped to the Docker container.
4. Build the project: ```./ci/publish-self-contained.sh```.
5. Test the project: ```lit ./integration-tests -vvv```.

## Alternative Quick Setup

```bash
# Build the required Docker images.
./ci/build-images.sh

# For development or use, start a tmp container. 
# The local repository's folder is shared with the container.
./ci/tmp-container.sh

## The following commands are executed in the container.

# Build SDC so it is available for the integration tests.
./ci/publish-self-contained.sh

# Run the integration tests.
# The files generated by the tests are available in integration-tests/output.
lit ./integration-tests -vvv
```

## Code Style

Before pushing, ensure that the code is formatted correctly; otherwise, the CI will fail.

```bash
dotnet format ./src/SMTDafnyCompiler.sln
```
