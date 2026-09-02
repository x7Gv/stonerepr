import Mathlib.Tactic

-- Määritellään tyyppiluokat liitolle ja kohtaamiselle
class MySup (P : Type) where
  sup : P → P → P

class MyInf (P : Type) where
  inf : P → P → P

-- Otetaan käyttöön symbolit
infixl:68 " ⊔ " => MySup.sup
infixl:69 " ⊓ " => MyInf.inf

-- Määritelmä 2.1.1 (Osittaisjärjestys).
class MyPartialOrder (P : Type) extends LE P where
  -- Refleksiivisyys
  le_refl : ∀ a : P, a ≤ a
  -- Antisymmetria
  le_antisymm : ∀ a b : P, a ≤ b → b ≤ a → a = b
  -- Transitiivisuus
  le_trans : ∀ a b c : P, a ≤ b → b ≤ c → a ≤ c

def Dual (P : Type) := P

def toDual {P : Type} (a : P) : Dual P := a
def ofDual {P : Type} (a : Dual P) : P := a

-- Lause 2.1.8 (Duaalijärjestys).
instance [MyPartialOrder P] : MyPartialOrder (Dual P) where
  -- Määritelmä
  le a b := ofDual b ≤ ofDual a
  le_refl a := MyPartialOrder.le_refl (ofDual a)
  le_antisymm a b h1 h2 :=
    MyPartialOrder.le_antisymm (ofDual a) (ofDual b) h2 h1
  le_trans a b c h1 h2 :=
    MyPartialOrder.le_trans (ofDual c) (ofDual b) (ofDual a) h2 h1

-- Määritelmä 2.1.10 (Hila (Järjestysteoreettinen)).
class OrderLattice (P : Type) extends MyPartialOrder P, MySup P, MyInf P where
-- Liitto
  le_sup_left : ∀ a b : P, a ≤ a ⊔ b
  le_sup_right : ∀ a b : P, b ≤ a ⊔ b
  sup_le : ∀ a b c : P, a ≤ c → b ≤ c → a ⊔ b ≤ c
-- Kohtaaminen
  inf_le_left : ∀ a b : P, a ⊓ b ≤ a
  inf_le_right : ∀ a b : P, a ⊓ b ≤ b
  le_inf : ∀ a b c : P, c ≤ a → c ≤ b → c ≤ a ⊓ b

-- Määritelmä 2.1.11 (Hila (Algebrallinen)).
class AlgebraicLattice (L : Type) extends MySup L, MyInf L where
  sup_comm : ∀ a b : L, a ⊔ b = b ⊔ a
  inf_comm : ∀ a b : L, a ⊓ b = b ⊓ a
  sup_assoc : ∀ a b c : L, a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c
  inf_assoc : ∀ a b c : L, a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c
  sup_inf_absorb : ∀ a b : L, a ⊔ (a ⊓ b) = a
  inf_sup_absorb : ∀ a b : L, a ⊓ (a ⊔ b) = a
  sup_idem : ∀ a : L, a ⊔ a = a
  inf_idem : ∀ a : L, a ⊓ a = a

-- Lemma 2.1.12 (1) a ≤ b joss a ⊔ b = b
lemma ord_iff_sup [OrderLattice P] (a b : P) : a ≤ b ↔ a ⊔ b = b := by
  constructor
  · intro aleb
    have hleft : b ≤ a ⊔ b := by
      exact OrderLattice.le_sup_right a b
    have hright : a ⊔ b ≤ b := by
      have hbb : b ≤ b := MyPartialOrder.le_refl b
      apply OrderLattice.sup_le
      · exact aleb
      exact hbb
    apply MyPartialOrder.le_antisymm
    · exact hright
    exact hleft
  · intro h_supb
    have h : a ≤ a ⊔ b := by
      exact OrderLattice.le_sup_left a b
    rw [← h_supb]
    exact h

-- Lemma 2.1.12 (2) a ≤ b joss a ⊓ b = a
theorem ord_iff_inf [OrderLattice P] (a b : P) : a ≤ b ↔ a ⊓ b = a := by
  constructor
  · intro hab
    have hright : a ⊓ b ≤ a := by
      exact OrderLattice.inf_le_left a b
    have hleft : a ≤ a ⊓ b := by
      have ha : a ≤ a := MyPartialOrder.le_refl a
      apply OrderLattice.le_inf
      · exact ha
      · exact hab
    apply MyPartialOrder.le_antisymm
    · exact hright
    · exact hleft
  intro h_infa
  have h : a ⊓ b ≤ b := by
    apply OrderLattice.inf_le_right
  rw [← h_infa]
  exact h

-- Lause 2.1.13 (1)
instance [OrderLattice P] : AlgebraicLattice P where
  sup_comm := by
    intro a b
    have h1 : b ⊔ a ≤ a ⊔ b := by
      have ha : a ≤ a ⊔ b := by
        exact OrderLattice.le_sup_left a b
      have hb : b ≤ a ⊔ b := by
        exact OrderLattice.le_sup_right a b
      exact OrderLattice.sup_le b a (a ⊔ b) hb ha
    have h2 : a ⊔ b ≤ b ⊔ a := by
      have ha : a ≤ b ⊔ a := by
        exact OrderLattice.le_sup_right b a
      have hb : b ≤ b ⊔ a := by
        exact OrderLattice.le_sup_left b a
      exact OrderLattice.sup_le a b (b ⊔ a) ha hb
    exact MyPartialOrder.le_antisymm (a ⊔ b) (b ⊔ a) h2 h1
  inf_comm := by
    sorry
  sup_assoc := by
    sorry
  inf_assoc := by
    sorry
  sup_inf_absorb := by
    intro a b
    have hleft : a ≤ a ⊔ (a ⊓ b) := by
      exact OrderLattice.le_sup_left a (a ⊓ b)
    have hright : a ⊔ (a ⊓ b) ≤ a := by
      have h1 : a≤ a := by
        exact MyPartialOrder.le_refl a
      have h2 : a⊓ b ≤ a := by
        exact OrderLattice.inf_le_left a b
      exact OrderLattice.sup_le a (a ⊓ b) a h1 h2
    exact MyPartialOrder.le_antisymm (a ⊔ a ⊓ b) a hright hleft
  inf_sup_absorb := by
    sorry
  sup_idem := by
    sorry
  inf_idem := by
    sorry

-- Lause 2.1.13 (2)
instance [AlgebraicLattice P] : OrderLattice P where
  le a b := a = a ⊓ b
  le_refl := by
    intro a
    exact Eq.symm (AlgebraicLattice.inf_idem a)
  le_antisymm := by
    intro a b ha hc
    have h : a ⊓ b = b ⊓ a := by
      exact AlgebraicLattice.inf_comm a b
    exact (rel_congr (id (Eq.symm ha)) (id (Eq.symm hc))).mp h
  le_trans := by
    intro a b c hab hbc
    have h1 : a ⊓ c = (a ⊓ b) ⊓ c := by
      rw [← hab]
    rw [← AlgebraicLattice.inf_assoc a] at h1
    rw [← hbc] at h1
    rw [← hab] at h1
    exact Eq.symm h1
  sup_le := by
    have l1 : ∀ x y : P, x = x ⊓ y ↔ y = x ⊔ y := by
      intro x y
      constructor
      · intro hxy
        have h1 := AlgebraicLattice.sup_inf_absorb y x
        rw [AlgebraicLattice.inf_comm y x] at h1
        rw [← hxy] at h1
        rw [AlgebraicLattice.sup_comm y x] at h1
        exact Eq.symm h1
      · intro hyx
        have h1 := AlgebraicLattice.inf_sup_absorb x y
        rw [← hyx] at h1
        exact Eq.symm h1
    intro a b c hac hbc
    have h1 : c = a ⊔ c := by
      exact Iff.elim (fun a_1 a ↦ a_1 hac) (l1 a c)
    have h2 : c = b⊔ c := by
      exact Iff.elim (fun a a_1 ↦ a hbc) (l1 b c)
    have h3 : a ⊔ b ⊔ c = c := by
      rw [← AlgebraicLattice.sup_assoc]
      rw [← h2]
      rw [← h1]
    exact Iff.elim (fun a_1 a_2 ↦ a_2 (id (Eq.symm h3))) (l1 (a ⊔ b) c)
  le_inf := by
    sorry
  le_sup_left := by
    intro a b
    exact Eq.symm (AlgebraicLattice.inf_sup_absorb a b)
  le_sup_right := by
    intro a b
    rw [AlgebraicLattice.sup_comm]
    exact Eq.symm (AlgebraicLattice.inf_sup_absorb b a)
  inf_le_left := by
    intro a b
    rw [AlgebraicLattice.inf_comm]
    rw [← AlgebraicLattice.inf_assoc]
    rw [AlgebraicLattice.inf_idem]
  inf_le_right := by
    intro a b
    rw [← AlgebraicLattice.inf_assoc]
    rw [AlgebraicLattice.inf_idem]

-- Määritellään pienimmän ja suurimman alkion tyyppiluokat ja merkintä

class MyBot (L : Type) where
  bot : L

class MyTop (L : Type) where
  top : L

notation "⊥" => MyBot.bot
notation "⊤" => MyTop.top

-- Määritelmä 2.2.1 (Rajoitettu hila).
class BoundedAlgebraicLattice (L : Type) extends AlgebraicLattice L, MyTop L, MyBot L where
  supTop : ∀ x : L, x ⊔ ⊤ = MyTop.top
  infBot : ∀ x : L, x ⊓ ⊥ = MyBot.bot
  supId : ∀ x : L, x ⊔ ⊥ = x
  infId : ∀ x : L, x ⊓ ⊤ = x

-- Määritelmä 2.2.2 (Komplementti)
def IsComplement [BoundedAlgebraicLattice L] (a x : L) : Prop :=
  a ⊔ x = MyTop.top ∧ a ⊓ x = MyBot.bot

-- Määritelmä 2.2.3 (Komplementtihila)
class ComplementedAlgebraicLattice (L : Type) extends BoundedAlgebraicLattice L where
  exists_comp : ∀ a : L, ∃ x : L, IsComplement a x

-- Määritelmä 2.2.4 (Boolen algebra).
class MyBooleanAlgebra (B : Type) extends ComplementedAlgebraicLattice B where
  sup_distrib : ∀ a b c : B, a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)
  inf_distrib : ∀ a b c : B, a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)

-- Lemma 2.2.4
lemma complement_unique [MyBooleanAlgebra B] (a x y : B)
  (hx : IsComplement a x) (hy : IsComplement a y) : x = y := by
  have x_le : x ≤ y := by
    have h : x = x ⊓ y := by
      calc
        x = x ⊔ (x ⊓ a) := by
          exact Eq.symm (AlgebraicLattice.sup_inf_absorb x a)
        _ = (x ⊔ x) ⊓ (x ⊔ a) := by
          exact MyBooleanAlgebra.sup_distrib x x a
        _ = (x) ⊓ (x ⊔ a) := by
          rw [AlgebraicLattice.sup_idem]
        _ = x ⊓ ( ⊤ ) := by
          rw [AlgebraicLattice.sup_comm, hx.left]
        _ = x ⊓ ( y ⊔ a ) := by
          rw [AlgebraicLattice.sup_comm, hy.left]
        _ = (x ⊓ y) ⊔ (x ⊓ a) := by
          exact MyBooleanAlgebra.inf_distrib x y a
        _ = (x ⊓ y) ⊔ ( ⊥ ) := by
          rw [AlgebraicLattice.inf_comm x a, hx.right]
        _ = (x ⊓ y) := by
          rw [BoundedAlgebraicLattice.supId]
    exact (ord_iff_inf x y).mpr (id (Eq.symm h))
  have y_le : y ≤ x := by
    have h : y = y ⊓ x := by
      calc
        y = y ⊔ (y ⊓ a) := by
          exact Eq.symm (AlgebraicLattice.sup_inf_absorb y a)
        _ = (y ⊔ y) ⊓ (y ⊔ a) := by
          exact MyBooleanAlgebra.sup_distrib y y a
        _ = (y) ⊓ (y ⊔ a) := by
          rw [AlgebraicLattice.sup_idem]
        _ = y ⊓ ( ⊤ ) := by
          rw [AlgebraicLattice.sup_comm, hy.left]
        _ = y ⊓ ( x ⊔ a ) := by
          rw [AlgebraicLattice.sup_comm, hx.left]
        _ = (y ⊓ x) ⊔ (y ⊓ a) := by
          exact MyBooleanAlgebra.inf_distrib y x a
        _ = (y ⊓ x) ⊔ ( ⊥ ) := by
          rw [AlgebraicLattice.inf_comm y a, hy.right]
        _ = (y ⊓ x) := by
          rw [AlgebraicLattice.inf_comm, BoundedAlgebraicLattice.supId]
    exact (ord_iff_inf y x).mpr (id (Eq.symm h))
  exact MyPartialOrder.le_antisymm x y x_le y_le

-- Määritelmä 2.2.5 (Boolen homomorfismi).
structure BooleanHom (B B' : Type) [MyBooleanAlgebra B] [MyBooleanAlgebra B'] where
  -- Kuvaus
  toFun : B → B'
  -- Säilyttää liiton
  map_sup : ∀ a b : B, toFun (a ⊔ b) = toFun a ⊔ toFun b
  -- Säilyttää kohtaamisen
  map_inf : ∀ a b : B, toFun (a ⊓ b) = toFun a ⊓ toFun b
  -- Säilyttää komplementin
  map_comp : ∀ a : B, IsComplement a a' → IsComplement (toFun a) (toFun a')

instance [MyBooleanAlgebra B] [MyBooleanAlgebra B'] :
  CoeFun (BooleanHom B B') (fun _ ↦ B → B') where
    coe h := h.toFun

-- Lause 2.2.9 (1)
lemma map_top [MyBooleanAlgebra B] [MyBooleanAlgebra B'] (h : BooleanHom B B') :
  h ⊤ = (⊤ : B') := by
  have ⟨x, hx⟩ := ComplementedAlgebraicLattice.exists_comp (⊤ : B)
  have hx_top : (⊤ : B) ⊔ x = (⊤ : B) := hx.left
  have hxx : IsComplement (h ⊤) (h x) := h.map_comp ⊤ hx
  have hhx_top : h ⊤ ⊔ h x = (⊤ : B') := by
    exact hxx.left
  have h_calc : h ⊤ = h ⊤ ⊔ h x := by
    rw [← hx_top]
    nth_rewrite 2 [hx_top]
    rw [h.map_sup]
  rw [hhx_top] at h_calc
  exact h_calc

-- Lause 2.2.9 (2)
lemma map_bot [MyBooleanAlgebra B] [MyBooleanAlgebra B'] (h : BooleanHom B B') :
  h ⊥ = (⊥ : B') := by
  have ⟨x, hx⟩ := ComplementedAlgebraicLattice.exists_comp (⊥ : B)
  have hx_bot : (⊥ : B) ⊓  x = (⊥ : B) := hx.right
  have hxx : IsComplement (h ⊥) (h x) := h.map_comp ⊥ hx
  have hhx_top : h ⊥ ⊓ h x = (⊥ : B') := by
    exact hxx.right
  have h_calc : h ⊥ = h ⊥ ⊓ h x := by
    rw [← hx_bot]
    nth_rewrite 2 [hx_bot]
    rw [h.map_inf]
  rw [hhx_top] at h_calc
  exact h_calc
