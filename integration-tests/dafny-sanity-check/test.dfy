// RUN: %dafny build %s -o %t.build/test.cs | %FileCheck --check-prefix=CHECK-BUILD %s
// RUN: %t.build/test | %FileCheck --check-prefix=CHECK-RUNTIME %s

// CHECK-BUILD: Dafny program verifier finished with 0 verified, 0 errors
// CHECK-RUNTIME: (42, 131)

method Main() { print (42,131), "\n"; }
