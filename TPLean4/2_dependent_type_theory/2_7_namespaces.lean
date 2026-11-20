/-
Namespaces provide a way to group definitions together and avoid name clashes.
-/
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- definitions inside the namespace are not in scope outside of the namespace
#check a
#check f

-- they can still be accessed using the namespace
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

-- we can open a namespace to bring its definitions into scope
open Foo

#check a
#check f
#check fa
#check Foo.fa

-- we can add definitions to an existing namespace
def Foo.b := 1
#check Foo.b
#check b -- works because Foo is open

-- however defining a new constant does not add it to the namespace
def c := 2
#check c
#check Foo.c

/-
But sometimes you will want to leave this information protected by a fully qualified name,
for example, when they conflict with identifiers in another namespace you want to use.

For example, Lean groups definitions and theorems involving lists into a namespace List.
-/
#check List.nil
#check List.cons
#check List.map


/-
Nested namespaces
-/

namespace Bar
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Buzz
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Buzz

  #check fa
  #check Buzz.ffa
end Bar

#check Bar.fa
#check Bar.Buzz.ffa

open Bar

#check fa
#check Buzz.ffa


/-
Namespaces can be reopened and extended later even in different files
-/

namespace Hello
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Hello

#check Hello.a
#check Hello.f

namespace Hello
  def ffa : Nat := f (f a)
end Hello

#check Hello.ffa
