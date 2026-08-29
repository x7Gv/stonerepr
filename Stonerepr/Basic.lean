import Mathlib.Tactic

section PartialOrders_and_Lattices

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
      exact ha
      exact hab
    apply MyPartialOrder.le_antisymm
    exact hright
    exact hleft
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
    have h : a ⊓ b = b⊓ a := by
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

section BooleanAlgebras

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

-- Määritelmä 2.3.1
structure MyFilter (L : Type) [OrderLattice L] [BoundedAlgebraicLattice L] where
  -- Osajoukko: F ⊆ L
  carrier : Set L
  -- Epätyhjyys: ⊤ ∈ F
  top_mem : (⊤ : L) ∈ carrier
  -- Ylöspäin suljettu
  upwards_closed : ∀ a b : L, a ∈ carrier → a ⊔ b = b → b ∈ carrier
  -- Suljettu kohtaamisen suhteen
  inf_mem : ∀ a b : L, a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier

variable {L : Type} [BoundedAlgebraicLattice L]
variable {B : Type} [MyBooleanAlgebra B]


instance : Membership L (MyFilter L) where
  mem F x := x ∈ F.carrier

def MyFilter.IsProper (F : MyFilter L) : Prop :=
  F.carrier ≠ Set.univ

-- Lemma 2.3.2
lemma proper_iff_bot_not_mem (F : MyFilter L) : F.IsProper ↔ (⊥ : L) ∉ F := by
  constructor
  · intro f_proper
    by_contra
    have L_sub : Set.univ ⊆ F.carrier := by
      intro a ha
      have h1 : a ⊔ ⊥ = a := by
        exact BoundedAlgebraicLattice.supId a
      apply MyFilter.upwards_closed F (⊥ : L) a
      · exact Set.mem_preimage.mp this
      rw [AlgebraicLattice.sup_comm]
      exact h1
    have F_sub : F.carrier ⊆ Set.univ := by
      exact Set.subset_univ F.carrier
    have hc : F.carrier = Set.univ := by
      exact Set.eq_univ_of_univ_subset L_sub
    contradiction
  · intro hnbot hc
    have h1 : (⊥ : L) ∈ Set.univ := by
      exact Set.mem_univ (⊥ : L)
    rw [← hc] at h1
    contradiction

-- Lemma 2.3.3
def filterGenSet (F : MyFilter B) (a : B) : Set B :=
  {x : B | ∃ f ∈ F, f ⊓ a ≤ x}

def filterGen (F : MyFilter B) (a : B) : MyFilter B where
  carrier := filterGenSet F a
  top_mem := by
    have h1 : ⊤ ∧ a = a := by
      exact And.symm ⟨rfl, trivial⟩
    have h2 : a ⊔ ⊤ = (⊤ : B) := by
      apply BoundedAlgebraicLattice.supTop
    have h3 : ∃ f ∈ F, f ⊓ a ≤ (⊤ : B) := by
      use ⊤
      constructor
      · apply MyFilter.top_mem
      exact OrderLattice.inf_le_left (⊤ : B) a
    exact Set.mem_preimage.mp h3
  upwards_closed := by
    intro x y hx hxy
    have hh1 : ∃ x' ∈ F, x' ⊓ a ≤ x := by
      exact Set.inter_nonempty.mp hx
    rcases hh1 with ⟨x', hx', hx''⟩
    have hh2 : x' ⊓ a ⊔ x = x := by
      exact (ord_iff_sup (x' ⊓ a) x).mp hx''
    have hh3 : x' ⊓ a ⊔ y = y := by
      calc
        x' ⊓ a ⊔ y = x' ⊓ a ⊔ (x ⊔ y) := by
          rw [hxy]
        _ = (x' ⊓ a ⊔ x) ⊔ y := by
          rw [AlgebraicLattice.sup_assoc]
        _ = x ⊔ y := by
          rw [hh2]
        _ = y := by
          exact hxy
    have hh4 : x' ⊓ a ≤ y := by
      exact (ord_iff_sup (x' ⊓ a) y).mpr hh3
    have hh5 : ∃ f ∈ F, f ⊓ a ≤ y := by
      use x'
    exact Set.mem_of_subset_of_mem (fun ⦃a_1⦄ a ↦ a) hh5
  inf_mem := by
    intro x y hx hy
    have hhx : ∃ x' ∈ F, x' ⊓ a ≤ x := by
      exact Set.inter_nonempty.mp hx
    have hhy : ∃ y' ∈ F, y' ⊓ a ≤ y := by
      exact Set.inter_nonempty.mp hy
    rcases hhx with ⟨x', hx', hx''⟩
    rcases hhy with ⟨y', hy', hy''⟩
    have hxx : (x' ⊓ y') ⊓ a ≤ x := by
      have h1 : (x' ⊓ y') ⊓ a = x'⊓ a ⊓ y' := by
        rw [← AlgebraicLattice.inf_assoc]
        rw [AlgebraicLattice.inf_comm y']
        rw [AlgebraicLattice.inf_assoc]
      have h2 : (x' ⊓ a) ⊓ y' ≤ (x' ⊓ a) := by
        exact OrderLattice.inf_le_left (x' ⊓ a) y'
      have h3 : (x' ⊓ a ) ≤ x := by
        exact le_of_eq_of_le rfl hx''
      rw [h1]
      exact MyPartialOrder.le_trans (x' ⊓ a ⊓ y') (x' ⊓ a) x h2 hx''
    have hyy : (x' ⊓ y') ⊓ a ≤ y := by
      have h1 : (x' ⊓ y') ⊓ a =y'⊓ a ⊓ x' := by
        rw [← AlgebraicLattice.inf_assoc]
        rw [AlgebraicLattice.inf_comm]
      have h2 : (y' ⊓ a) ⊓ x' ≤ (y' ⊓ a) := by
        exact OrderLattice.inf_le_left (y' ⊓ a) x'
      have h3 : (x' ⊓ a ) ≤ x := by
        exact le_of_eq_of_le rfl hx''
      rw [h1]
      exact MyPartialOrder.le_trans (y' ⊓ a ⊓ x') (y' ⊓ a) y h2 hy''
    have hhxxyy : x' ⊓ y' ⊓ a ≤ x ⊓ y := by
      exact OrderLattice.le_inf x y (x' ⊓ y' ⊓ a) hxx hyy
    have hex : ∃ f ∈ F, f ⊓ a ≤ x ⊓ y := by
      use x' ⊓ y'
      constructor
      · apply F.inf_mem
        · exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hx'
        · exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hy'
      exact hhxxyy
    exact Set.mem_preimage.mp hex

-- Määritelmä 2.3.5
structure MyUltraFilter
  (L : Type)
  [OrderLattice L]
  [BoundedAlgebraicLattice L] extends MyFilter L where
  proper : carrier ≠ Set.univ
  maximal : ∀ U : MyFilter L, carrier ⊆ U.carrier → (U.carrier = Set.univ ∨ U.carrier = carrier)

-- Apulemma: Jos filtteri sisältää alkion a ja sen komplementin x, se sisältää ⊥:n
lemma filter_bot_mem_of_comp_mem {B : Type} [MyBooleanAlgebra B]
  (F : MyFilter B) (a x : B) (hcomp : IsComplement a x)
  (ha : a ∈ F.carrier) (hx : x ∈ F.carrier) : (⊥ : B) ∈ F.carrier := by
  have h_inf : a ⊓ x ∈ F.carrier := F.inf_mem a x ha hx
  have h_bot : a ⊓ x = (⊥ : B) := hcomp.right
  rwa [h_bot] at h_inf

-- Apulemma: Jos ⊥ ∈ F.carrier, niin F.carrier = Set.univ
lemma filter_univ_of_bot_mem {B : Type} [MyBooleanAlgebra B]
  (F : MyFilter B) (hbot : (⊥ : B) ∈ F.carrier) : F.carrier = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro x _
  have h_sup : (⊥ : B) ⊔ x = x := by
    rw [AlgebraicLattice.sup_comm]
    exact BoundedAlgebraicLattice.supId x
  exact F.upwards_closed ⊥ x hbot h_sup

-- Lause 2.3.6 (1)
theorem ultrafilter_char_1
  (U : MyUltraFilter B) (a x : B) (hcomp : IsComplement a x) :
  a ∈ U.carrier ↔ x ∉ U.carrier := by
  constructor
  · intro ha
    by_contra
    have hbot : (⊥ : B) ∈ U.carrier := by
      have h_axcomp : a ⊓ x = (⊥ : B) := by
        exact hcomp.right
      exact filter_bot_mem_of_comp_mem U.toMyFilter a x hcomp ha this
    have huniv : U.carrier = Set.univ := by
      exact filter_univ_of_bot_mem U.toMyFilter hbot
    have hc : U.carrier ≠ Set.univ := by
      exact U.proper
    contradiction
  · intro hna
    by_contra
    let Ua := filterGen U.toMyFilter a
    have hUa_proper : Ua.carrier ≠ Set.univ := by
      intro hUa_univ
      have hbot_in : (⊥ : B) ∈ Ua.carrier := by
        rw [hUa_univ]
        exact Set.mem_univ (⊥ : B)
      have hex : ∃ f ∈ U.carrier, f ⊓ a ≤ (⊥ : B) := hbot_in
      rcases hex with ⟨f, hf, hfa⟩
      have hbotleq : (⊥ : B) ≤ f ⊓ a := by
        have haux : (⊥ : B) ⊓ (f ⊓ a) = (⊥ : B) := by
          rw [AlgebraicLattice.inf_comm]
          exact BoundedAlgebraicLattice.infBot (f ⊓ a)
        exact (ord_iff_inf (⊥ : B) (f ⊓ a)).mpr haux
      have h_botfa : (⊥ : B) = f⊓ a := by
        exact MyPartialOrder.le_antisymm (⊥ : B) (f ⊓ a) hbotleq hfa
      have hff : f = f ⊓ x := by
        calc
          f = f ⊓ ⊤ := by
            exact Eq.symm (BoundedAlgebraicLattice.infId f)
          _ = f ⊓ (a ⊔ x) := by
            have hh : a ⊔ x = (⊤ : B) := by
              apply hcomp.left
            rw [hh]
          _ = f ⊓ a ⊔ f ⊓ x := by
            exact MyBooleanAlgebra.inf_distrib f a x
          _ = (⊥ : B) ⊔ (f ⊓ x) := by
            rw [h_botfa]
          _ = f ⊓ x := by
            rw [AlgebraicLattice.sup_comm]
            exact BoundedAlgebraicLattice.supId (f ⊓ x)
      have hxx : x ∈ U.carrier := by
        apply MyFilter.upwards_closed U.toMyFilter f x hf
        exact (ord_iff_sup f x).mp hff
      contradiction
    have hUa_sub : U.carrier ⊆ Ua.carrier := by
      intro u hu
      have h : ∃ f ∈ U.carrier, f ⊓ a ≤ u := by
        use u
        constructor
        · exact hu
        exact OrderLattice.inf_le_left u a
      exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) h
    have hor : Ua.carrier = Set.univ ∨ Ua.carrier = U.carrier := by
      apply MyUltraFilter.maximal U Ua hUa_sub
    have hn_or : ¬(Ua.carrier = Set.univ ∨ Ua.carrier = U.carrier) := by
      push Not
      constructor
      · exact Ne.symm (Ne.intro (id (Ne.symm hUa_proper)))
      have haux : ∃ x ∈ Ua, x ∉ U.carrier := by
        have ha : a ∈ Ua.carrier := by
          have hex : ∃ f ∈ U.carrier, f ⊓ a ≤ a := by
            use ⊤
            constructor
            · exact U.top_mem
            exact OrderLattice.inf_le_right (⊤ : B) a
          exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hex
        exact Set.not_subset.mp fun a_1 ↦ this (a_1 ha)
      intro ha
      rcases haux with ⟨c, hc, hcc⟩
      have haux : c ∈ Ua.carrier := by
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hc
      rw [← ha] at hcc
      contradiction
    contradiction

-- Lause 2.3.6 (2)
def ultrafilter_char_2
  (U : MyFilter B)
  (h : ∀ a x : B, IsComplement a x → a ∈ U.carrier ↔ x ∉ U.carrier) :
  MyUltraFilter B where
  carrier := U.carrier
  top_mem := U.top_mem
  upwards_closed := U.upwards_closed
  inf_mem := U.inf_mem
  proper := by
    intro hUniv
    have hbotmem : (⊥ : B) ∈ U.carrier := by
      have haux : (⊥ : B) ∈ Set.univ := by
        exact Set.mem_univ (⊥ : B)
      rw [hUniv]
      exact haux
    have hBot_comp : IsComplement (⊥ : B) ⊤ := by
      constructor
      · exact BoundedAlgebraicLattice.supTop (⊥ : B)
      · exact BoundedAlgebraicLattice.infId (⊥ : B)
    have hntop : ¬((⊤ : B) ∈ U.carrier) := by
      apply (h (⊥ : B) (⊤ : B)).mp
      intro _
      exact hbotmem
    have hc : (⊤ : B) ∈ U.carrier := by
      exact U.top_mem
    contradiction
  maximal := by
    by_contra
    push Not at this
    rcases this with ⟨F, hf, ⟨hff1, hff2⟩⟩
    have hnotempty : F.carrier ≠ ∅ := by
      intro hc
      have haux : (⊤ : B) ∈ F.carrier := by
        exact F.top_mem
      have hc : (⊤ : B) ∉ F.carrier := by
        exact Eq.mpr_not (congrFun hc ⊤) fun a ↦ a
      contradiction
    have hex : ∃x ∈ F.carrier, x ∉ U.carrier := by
      apply Set.not_subset.mp
      intro hc
      have hc_eq : F.carrier = U.carrier := by
        exact Set.Subset.antisymm hc hf
      contradiction
    rcases hex with ⟨x, hx, hxx⟩
    have ⟨comp_x, hcomp_x⟩ := ComplementedAlgebraicLattice.exists_comp x
    have hcomp_symm : IsComplement comp_x x := by
      constructor
      · rw [AlgebraicLattice.sup_comm]
        exact hcomp_x.left
      · rw [AlgebraicLattice.inf_comm]
        exact hcomp_x.right
    have hcomp_xU : comp_x ∈ U.carrier := by
      apply (h comp_x x).mpr
      · exact hxx
      exact hcomp_symm
    have hcomp_xF : comp_x ∈ F.carrier := by
      exact Set.mem_of_subset_of_mem hf hcomp_xU
    have hbot : (⊥ : B) ∈ F.carrier := by
      have haux : x ⊓ comp_x = (⊥ : B) := by
        exact hcomp_x.right
      have haux2 : x ⊓ comp_x ∈ F.carrier := by
        exact F.inf_mem x comp_x hx (hf hcomp_xU)
      rw [← haux]
      exact haux2
    have hc : F.carrier = Set.univ := by
      exact filter_univ_of_bot_mem F hbot
    contradiction
