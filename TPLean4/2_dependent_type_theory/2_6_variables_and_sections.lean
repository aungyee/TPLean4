/-
we can declare variables that are in scope till the end of the file
-/

variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))


/-
variables can be declared for any type
-/

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose2 := g (f x)
def doTwice2 := h (h x)
def doThrice2 := h (h (h x))

#print compose
#print compose2
#print doTwice
#print doTwice2
#print doThrice
#print doThrice2


/-
Sometimes, it is useful to limit the scope of a variable. Lean provides the notion of a section:
-/

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose3 := g (f x)
  def doTwice3 := h (h x)
  def doThrice3 := h (h (h x))
end useful

-- indentation is not required, but makes it easier to see the scope of the section
-- and the name of the section does not matter

section useful
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose4 := g (f x)
def doTwice4 := h (h x)
def doThrice4 := h (h (h x))
end useful

-- section does not require a name and does not create a namespace
section
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose5 := g (f x)
  def doTwice5 := h (h x)
  def doThrice5 := h (h (h x))
end
