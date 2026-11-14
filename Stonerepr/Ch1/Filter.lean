import Mathlib.Tactic

import Stonerepr.Ch1.Algebra

-- Määritelmä 2.3.1
structure MyFilter (L : Type) [BoundedAlgebraicLattice L] where
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

instance : Std.Commutative (fun (a b : L) => a ⊓ b) where
  comm := AlgebraicLattice.inf_comm

instance : Std.Associative (fun (a b : L) => a ⊓ b) where
  assoc := fun a b c ↦ Eq.symm (AlgebraicLattice.inf_assoc a b c)

def finsetInf (L : Type) [BoundedAlgebraicLattice L] (T : Finset L) : L :=
  T.fold (· ⊓ ·) (⊤ : L) id

lemma finsetInf_empty (L : Type) [BoundedAlgebraicLattice L] :
    finsetInf L ∅ = (⊤ : L) := rfl

lemma finsetInf_singleton (L : Type) [BoundedAlgebraicLattice L] (a : L) :
    finsetInf L {a} = a := by
  simp [finsetInf, BoundedAlgebraicLattice.infId]

lemma finsetInf_insert_of_notMem (L : Type) [BoundedAlgebraicLattice L] [DecidableEq L]
    {a : L} {s : Finset L} (ha : a ∉ s) :
    finsetInf L (insert a s) = a ⊓ finsetInf L s :=
  Finset.fold_insert ha

lemma finsetInf_le_of_mem (L : Type) [BoundedAlgebraicLattice L]
    {s : Finset L} {a : L} (ha : a ∈ s) :
    finsetInf L s ≤ a := by
  classical
  induction s using Finset.induction with
  | empty => exact absurd ha (Finset.notMem_empty a)
  | insert x s hx ih =>
    rw [finsetInf_insert_of_notMem L hx]
    rcases Finset.mem_insert.mp ha with rfl | has
    · exact OrderLattice.inf_le_left a (finsetInf L s)
    · exact MyPartialOrder.le_trans (x ⊓ finsetInf L s) (finsetInf L s) a
        (OrderLattice.inf_le_right x (finsetInf L s)) (ih has)

lemma finsetInf_insert (L : Type) [BoundedAlgebraicLattice L] [DecidableEq L]
    (a : L) (s : Finset L) :
    finsetInf L (insert a s) = a ⊓ finsetInf L s := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    have hle : finsetInf L s ≤ a := finsetInf_le_of_mem L ha
    have heq : finsetInf L s ⊓ a = finsetInf L s := (ord_iff_inf (finsetInf L s) a).mp hle
    rw [AlgebraicLattice.inf_comm a (finsetInf L s), heq]
  · exact finsetInf_insert_of_notMem L ha

lemma finsetInf_union (L : Type) [BoundedAlgebraicLattice L] [DecidableEq L]
    (Ta Tb : Finset L) :
    finsetInf L (Ta ∪ Tb) = finsetInf L Ta ⊓ finsetInf L Tb := by
  induction Ta using Finset.induction with
  | empty =>
    rw [Finset.empty_union, finsetInf_empty, AlgebraicLattice.inf_comm (⊤ : L),
      BoundedAlgebraicLattice.infId]
  | insert a Ta _ ih =>
    rw [Finset.insert_union, finsetInf_insert, finsetInf_insert, ih, AlgebraicLattice.inf_assoc]

def HasFIP (L : Type) [BoundedAlgebraicLattice L] (S : Set L) : Prop :=
  ∀ (T : Finset L), (∀ x ∈ T, x ∈ S) → finsetInf L T ≠ (⊥ : L)

def filterGenSetFromSet (L : Type) [BoundedAlgebraicLattice L] (S : Set L) : Set L :=
  {x : L | ∃ (T : Finset L), (∀ s ∈ T, s ∈ S) ∧ finsetInf L T ≤ x}

-- Lemma 2.3.3
def filterGenSet (F : MyFilter B) (a : B) : Set B :=
  {x : B | ∃ f ∈ F, f ⊓ a ≤ x}

open Classical in
def filtGen (L : Type) [BoundedAlgebraicLattice L] (S : Set L) (hS : S.Nonempty) : MyFilter L where
  carrier := filterGenSetFromSet L S
  top_mem := by
    rcases hS with ⟨s, hs⟩
    refine ⟨{s}, ?_, ?_⟩
    · intro s' hs'
      rw [Finset.mem_singleton.mp hs']
      exact hs
    · rw [finsetInf_singleton]
      exact (ord_iff_sup s (⊤ : L)).mpr (BoundedAlgebraicLattice.supTop s)
  upwards_closed := by
    intro a b ⟨T, hTs, hTa⟩ hab
    exact ⟨T, hTs, MyPartialOrder.le_trans (finsetInf L T) a b hTa ((ord_iff_sup a b).mpr hab)⟩
  inf_mem := by
    intro a b ⟨Ta, hTa1, hTa2⟩ ⟨Tb, hTb1, hTb2⟩
    refine ⟨Ta ∪ Tb, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_union.mp hs with hsTa | hsTb
      · exact hTa1 s hsTa
      · exact hTb1 s hsTb
    · rw [finsetInf_union]
      have haa : finsetInf L Ta ⊓ finsetInf L Tb ≤ a :=
        MyPartialOrder.le_trans _ (finsetInf L Ta) a
          (OrderLattice.inf_le_left (finsetInf L Ta) (finsetInf L Tb)) hTa2
      have hbb : finsetInf L Ta ⊓ finsetInf L Tb ≤ b :=
        MyPartialOrder.le_trans _ (finsetInf L Tb) b
          (OrderLattice.inf_le_right (finsetInf L Ta) (finsetInf L Tb)) hTb2
      exact OrderLattice.le_inf a b (finsetInf L Ta ⊓ finsetInf L Tb) haa hbb

-- Lemma 2.3.3 (2): ⟨S⟩ on aito joss S:llä on äärellisten kohtaamisten ominaisuus
theorem filtGen_isProper_iff_hasFIP (L : Type) [BoundedAlgebraicLattice L]
    (S : Set L) (hS : S.Nonempty) :
    (filtGen L S hS).IsProper ↔ HasFIP L S := by
  rw [proper_iff_bot_not_mem]
  constructor
  · intro hbot T hTs hinf_bot
    apply hbot
    refine ⟨T, hTs, ?_⟩
    rw [hinf_bot]
    exact MyPartialOrder.le_refl (⊥ : L)
  · intro hfip ⟨T, hTs, hT_le_bot⟩
    apply hfip T hTs
    have hbot_le : (⊥ : L) ≤ finsetInf L T := by
      have haux : (⊥ : L) ⊓ finsetInf L T = (⊥ : L) := by
        rw [AlgebraicLattice.inf_comm]
        exact BoundedAlgebraicLattice.infBot (finsetInf L T)
      exact (ord_iff_inf (⊥ : L) (finsetInf L T)).mpr haux
    exact MyPartialOrder.le_antisymm (finsetInf L T) (⊥ : L) hT_le_bot hbot_le

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

lemma ultrafilter_mem_iff_compl_notMem (U : MyUltraFilter B) (a : B) :
    a ∈ U.carrier ↔ aᶜ ∉ U.carrier :=
  ultrafilter_char_1 U a aᶜ (MyBooleanAlgebra.compl_isComplement a)

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
