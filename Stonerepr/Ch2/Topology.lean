import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Stonerepr.Ch1

variable {B : Type} [ThesisBooleanAlgebra B]

-- Määritelmä 3.2.2: Ultrafilttereiden joukko Ult(B) ja kanta-alkiot S_a
abbrev Ult (B : Type) [ThesisBooleanAlgebra B] := ThesisUltrafilter B

def stoneBasic (a : B) : Set (Ult B) :=
  {U | a ∈ U.carrier}

def stoneBasis (B : Type) [ThesisBooleanAlgebra B] : Set (Set (Ult B)) :=
  Set.range (stoneBasic (B := B))

-- Lemma 3.2.3: Boolen operaatioiden ja kanta-alkioiden vastaavuudet
lemma stoneBasic_top : stoneBasic (⊤ : B) = Set.univ := by
    ext U
    have h : (⊤ : B) ∈ U.carrier := by
        exact U.top_mem
    constructor
    ·   intro uTop
        exact Set.mem_univ U
    intro uUniv
    unfold stoneBasic
    exact Set.mem_ofPred.mpr h

lemma stoneBasic_bot : stoneBasic (⊥ : B) = ∅ := by
  ext U
  constructor
  · intro uBot
    unfold stoneBasic at uBot
    have hc : (⊥ : B) ∈ U.carrier := by
      exact Set.mem_preimage.mp uBot
    have hc' : (⊥ : B) ∉ U.carrier := by
      apply (proper_iff_bot_not_mem U.toThesisFilter).mp
      apply U.proper
    contradiction
  · intro h
    exact Set.not_notMem.mp fun a ↦ h


lemma stoneBasic_sup (a b : B) :
    stoneBasic (a ⊔ b) = stoneBasic a ∪ stoneBasic b := by
  ext U
  constructor
  · intro hab
    have h : a⊔ b ∈ U.carrier := by
      exact Set.mem_preimage.mp hab
    by_contra hc
    have hh : U ∉ stoneBasic a ∧ U ∉ stoneBasic b := by
      exact not_or.mp hc
    have hh' : a ∉ U.carrier ∧ b ∉ U.carrier := by
      exact not_or.mp hc
    have hh'' : (aᶜ) ∈ U.carrier ∧ (bᶜ) ∈ U.carrier := by
      have hac : ∀ c : B, cᶜ ∈ U.carrier ↔ c ∉ U.carrier := by
        intro c
        have hh : ∀ c : B, c = (cᶜ)ᶜ := by
          intro c
          exact Eq.symm <| ThesisBooleanAlgebra.compl_compl c
        nth_rw 2 [hh c]
        exact ultrafilter_mem_iff_compl_notMem U cᶜ
      constructor
      · apply (hac a).mpr
        exact hh.1
      · apply (hac b).mpr
        exact hh.2
    have h3 : aᶜ ⊓ bᶜ ∈ U.carrier := by
      apply ThesisFilter.inf_mem
      · exact hh''.1
      · exact hh''.2
    have h4 : (a ⊔ b)ᶜ ∈ U.carrier := by
      have hc : aᶜ ⊓ bᶜ = (a ⊔ b)ᶜ := by
        exact Eq.symm (ThesisBooleanAlgebra.compl_sup_eq a b)
      rw [← hc]
      exact h3
    have hc : (⊥ : B) ∈ U.carrier := by
      have hh : (a ⊔ b) ⊓ (a ⊔ b)ᶜ ∈ U.carrier := by
        exact U.inf_mem (a ⊔ b) (a ⊔ b)ᶜ hab h4
      have hh' : (⊥ : B) = (a ⊔ b) ⊓ (a ⊔ b)ᶜ := by
        exact Eq.symm (ThesisBooleanAlgebra.compl_inf (a ⊔ b))
      rw [hh']
      exact hh
    have hc' : ¬ ((⊥ : B) ∈ U.carrier) := by
      apply (proper_iff_bot_not_mem U.toThesisFilter).mp
      apply U.proper
    contradiction
  · intro h
    have hh : U ∈ stoneBasic a ∨ U ∈ stoneBasic b := by
      exact (Set.mem_union U (stoneBasic a) (stoneBasic b)).mp h
    cases' hh with ha hb
    · unfold stoneBasic at ha
      have ha' : a ∈ U.carrier := by
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) ha
      have h1 : a ⊔ (a ⊔ b) = (a ⊔ b)  := by
        have h1' : a ≤ a ⊔ b := by
          exact OrderLattice.le_sup_left a b
        exact (ord_iff_sup a (a ⊔ b)).mp h1'
      have h2 : a ⊔ b ∈ U.carrier := by
        exact U.upwards_closed a (a ⊔ b) ha h1
      exact Set.mem_preimage.mp h2
    · unfold stoneBasic at hb
      have hb' : b ∈ U.carrier := by
        exact Set.mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hb
      have h1 : b ⊔ (a ⊔ b) = (a ⊔ b)  := by
        have h1' : b ≤ a ⊔ b := by
          exact OrderLattice.le_sup_right a b
        exact (ord_iff_sup b (a ⊔ b)).mp h1'
      have h2 : a ⊔ b ∈ U.carrier := by
        exact U.upwards_closed b (a ⊔ b) hb h1
      exact Set.mem_preimage.mp h2



lemma stoneBasic_inf (a b : B) :
    stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b := by
  ext U
  constructor
  · intro h
    have hab : a ⊓ b ∈ U.carrier := h
    have ha : a ∈ U.carrier :=
      U.upwards_closed (a ⊓ b) a hab ((ord_iff_sup (a ⊓ b) a).mp (OrderLattice.inf_le_left a b))
    have hb : b ∈ U.carrier :=
      U.upwards_closed (a ⊓ b) b hab ((ord_iff_sup (a ⊓ b) b).mp (OrderLattice.inf_le_right a b))
    exact ⟨ha, hb⟩
  · intro ⟨ha, hb⟩
    exact U.inf_mem a b ha hb

lemma stoneBasic_compl (a : B) :
    (stoneBasic a)ᶜ = stoneBasic (aᶜ) := by
  ext U
  change a ∉ U.carrier ↔ aᶜ ∈ U.carrier
  rw [ultrafilter_mem_iff_compl_notMem, not_not]

-- Stone-avaruuden topologia kanta-alkioiden virittämänä
instance instTopologicalSpaceUlt (B : Type) [ThesisBooleanAlgebra B] :
    TopologicalSpace (Ult B) :=
  TopologicalSpace.generateFrom (stoneBasis B)

lemma stoneBasis_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis (stoneBasis B) := by
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (t := instTopologicalSpaceUlt B) (r := stoneBasis B) rfl
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a ⊓ b, stoneBasic_inf a b⟩)
  have huniv : (Set.univ : Set (Ult B)) ∈ stoneBasis B := ⟨⊤, stoneBasic_top⟩
  rwa [Set.insert_eq_of_mem huniv] at h

lemma stoneBasic_isOpen (a : B) : IsOpen (stoneBasic a) :=
  stoneBasis_isTopologicalBasis.isOpen ⟨a, rfl⟩

lemma stoneBasic_isClosed (a : B) : IsClosed (stoneBasic a) := by
  rw [← isOpen_compl_iff, stoneBasic_compl]
  exact stoneBasic_isOpen (aᶜ)

-- Lemma 3.2.4: Kanta-alkiot ovat suljettu-avoimia
lemma stoneBasic_isClopen (a : B) : IsClopen (stoneBasic a) :=
  ⟨stoneBasic_isClosed a, stoneBasic_isOpen a⟩

-- Lemma 3.2.5: Ult(B) on Hausdorffin avaruus
instance instT2SpaceUlt (B : Type) [ThesisBooleanAlgebra B] : T2Space (Ult B) := by
  refine ⟨fun U₁ U₂ hne ↦ ?_⟩
  have hcar : U₁.carrier ≠ U₂.carrier := fun h ↦ hne (by
    cases U₁; cases U₂
    congr 1
    exact ThesisFilter.ext _ _ h)
  have hsep : (∃ a ∈ U₁.carrier, a ∉ U₂.carrier) ∨ (∃ a ∈ U₂.carrier, a ∉ U₁.carrier) := by
    by_contra h
    push Not at h
    exact hcar (Set.Subset.antisymm h.1 h.2)
  rcases hsep with ⟨a, ha1, ha2⟩ | ⟨a, ha2, ha1⟩
  · have ha2c : aᶜ ∈ U₂.carrier := by
      by_contra hc
      exact ha2 ((ultrafilter_mem_iff_compl_notMem U₂ a).mpr hc)
    refine ⟨stoneBasic a, stoneBasic (aᶜ), stoneBasic_isOpen a, stoneBasic_isOpen (aᶜ),
      ha1, ha2c, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty, ← stoneBasic_inf, ThesisBooleanAlgebra.compl_inf,
      stoneBasic_bot]
  · have ha1c : aᶜ ∈ U₁.carrier := by
      by_contra hc
      exact ha1 ((ultrafilter_mem_iff_compl_notMem U₁ a).mpr hc)
    refine ⟨stoneBasic (aᶜ), stoneBasic a, stoneBasic_isOpen (aᶜ), stoneBasic_isOpen a,
      ha1c, ha2, ?_⟩
    rw [Set.disjoint_iff_inter_eq_empty, ← stoneBasic_inf, AlgebraicLattice.inf_comm,
      ThesisBooleanAlgebra.compl_inf, stoneBasic_bot]

private lemma finsetInf_mem_of_mem (F : ThesisFilter B) (T : Finset B)
    (hT : ∀ b ∈ T, b ∈ F.carrier) : finsetInf B T ∈ F.carrier := by
  classical
  induction T using Finset.induction with
  | empty => exact F.top_mem
  | insert a s ha ih =>
    rw [finsetInf_insert_of_notMem B ha]
    exact F.inf_mem a (finsetInf B s) (hT a (Finset.mem_insert_self a s))
      (ih fun b hb ↦ hT b (Finset.mem_insert_of_mem hb))

-- Lemma 3.2.6: Ult(B) on kompakti
instance instCompactSpaceUlt (B : Type) [ThesisBooleanAlgebra B] : CompactSpace (Ult B) := by
  refine ⟨isCompact_iff_finite_subfamily_closed.mpr ?_⟩
  intro ι t ht_closed h_all
  by_contra! h_fin
  have h_fin_nonempty : ∀ u : Finset ι, (⋂ i ∈ u, t i).Nonempty := by
    intro u
    have hu := h_fin u
    rwa [Set.univ_inter] at hu
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    let Aᵢ : ι → Set B := fun i ↦ {b : B | t i ⊆ stoneBasic b}
    have ht_eq : ∀ i, t i = ⋂ b ∈ Aᵢ i, stoneBasic b := by
      intro i
      apply Set.Subset.antisymm
      · intro U hU
        exact Set.mem_iInter₂.mpr fun b hb ↦ hb hU
      · intro U hU
        by_contra hU_not
        have h_open : IsOpen (t i)ᶜ := (ht_closed i).isOpen_compl
        rcases stoneBasis_isTopologicalBasis.isOpen_iff.mp h_open U hU_not with
          ⟨_, ⟨a, rfl⟩, haU, ha_sub⟩
        have h_sub_compl : t i ⊆ stoneBasic (aᶜ) := by
          intro V hV
          rw [← stoneBasic_compl]
          exact fun hVa ↦ ha_sub hVa hV
        have hU_compl : U ∈ stoneBasic (aᶜ) := Set.mem_iInter₂.mp hU (aᶜ) h_sub_compl
        rw [← stoneBasic_compl] at hU_compl
        exact hU_compl haU
    let A : Set B := ⋃ i, Aᵢ i
    have hA_nonempty : A.Nonempty := by
      refine ⟨⊤, Set.mem_iUnion.mpr ⟨i₀, ?_⟩⟩
      intro U _
      rw [stoneBasic_top]
      exact Set.mem_univ U
    have hA_fip : HasFIP B A := by
      classical
      intro T hTA
      have h_choose : ∀ b ∈ T, ∃ i, b ∈ Aᵢ i := fun b hb ↦ Set.mem_iUnion.mp (hTA b hb)
      let u : Finset ι := T.attach.image fun b ↦ Classical.choose (h_choose b.1 b.2)
      rcases h_fin_nonempty u with ⟨U, hU⟩
      have hT_U : ∀ b ∈ T, b ∈ U.carrier := by
        intro b hb
        have hi : Classical.choose (h_choose b hb) ∈ u :=
          Finset.mem_image_of_mem _ (Finset.mem_attach T ⟨b, hb⟩)
        have hUi : U ∈ t (Classical.choose (h_choose b hb)) := Set.mem_iInter₂.mp hU _ hi
        exact (Classical.choose_spec (h_choose b hb)) hUi
      intro hbot
      have hbot_U : (⊥ : B) ∈ U.carrier := hbot ▸ finsetInf_mem_of_mem U.toThesisFilter T hT_U
      exact (proper_iff_bot_not_mem U.toThesisFilter).mp U.proper hbot_U
    have h_proper : (filtGen B A hA_nonempty).IsProper :=
      (filtGen_isProper_iff_hasFIP B A hA_nonempty).mpr hA_fip
    rcases ultrafilter_exists (filtGen B A hA_nonempty) h_proper with ⟨U, hU⟩
    have hU_mem : U ∈ Set.univ ∩ ⋂ i, t i := by
      refine ⟨Set.mem_univ U, Set.mem_iInter.mpr fun i ↦ ?_⟩
      rw [ht_eq i]
      refine Set.mem_iInter₂.mpr fun b hb ↦ hU ?_
      refine ⟨{b}, fun s hs ↦ ?_, ?_⟩
      · rw [Finset.mem_singleton.mp hs]
        exact Set.mem_iUnion.mpr ⟨i, hb⟩
      · rw [finsetInf_singleton]
        exact ThesisPartialOrder.le_refl b
    rw [h_all] at hU_mem
    exact hU_mem
  · have h_empty : IsEmpty ι := not_nonempty_iff.mp hι
    have h_empty_inter : (Set.univ ∩ ⋂ i, t i) = Set.univ := by simp [Set.iInter_of_empty]
    rw [h_empty_inter] at h_all
    have h_univ := h_fin_nonempty ∅
    simp [h_all] at h_univ

-- Määritelmä 3.2.1: Stone-avaruus
structure IsStoneSpace (X : Type) [TopologicalSpace X] : Prop where
  t2 : T2Space X
  compact : CompactSpace X
  clopen_basis : ∃ ℬ : Set (Set X),
    TopologicalSpace.IsTopologicalBasis ℬ ∧ ∀ U ∈ ℬ, IsClopen U

-- Lause 3.2.7: (Ult(B), τ_S) on Stone-avaruus
theorem ult_isStoneSpace : IsStoneSpace (Ult B) where
  t2 := instT2SpaceUlt B
  compact := instCompactSpaceUlt B
  clopen_basis := ⟨stoneBasis B, stoneBasis_isTopologicalBasis, by
    rintro _ ⟨a, rfl⟩
    exact stoneBasic_isClopen a⟩

-- Määritelmä 3.3.1: Suljettu-avointen joukkojen Boolen alialgebra
abbrev ClopenSet (X : Type) [TopologicalSpace X] := {A : Set X // IsClopen A}

instance instThesisBooleanAlgebraClopenSet (X : Type) [TopologicalSpace X] :
    ThesisBooleanAlgebra (ClopenSet X) where
  sup A B := ⟨A.1 ∪ B.1, A.2.union B.2⟩
  inf A B := ⟨A.1 ∩ B.1, A.2.inter B.2⟩
  top := ⟨Set.univ, isClopen_univ⟩
  bot := ⟨∅, isClopen_empty⟩
  sup_comm A B := Subtype.ext (Set.union_comm A.1 B.1)
  inf_comm A B := Subtype.ext (Set.inter_comm A.1 B.1)
  sup_assoc A B C := Subtype.ext (Set.union_assoc A.1 B.1 C.1).symm
  inf_assoc A B C := Subtype.ext (Set.inter_assoc A.1 B.1 C.1).symm
  sup_inf_absorb A B := Subtype.ext (by ext x; simp; tauto)
  inf_sup_absorb A B := Subtype.ext (by ext x; simp; tauto)
  sup_idem A := Subtype.ext (Set.union_self A.1)
  inf_idem A := Subtype.ext (Set.inter_self A.1)
  supTop A := Subtype.ext (Set.union_univ A.1)
  infBot A := Subtype.ext (Set.inter_empty A.1)
  supId A := Subtype.ext (Set.union_empty A.1)
  infId A := Subtype.ext (Set.inter_univ A.1)
  exists_comp A := ⟨⟨A.1ᶜ, A.2.compl⟩,
    Subtype.ext (Set.union_compl_self A.1), Subtype.ext (Set.inter_compl_self A.1)⟩
  compl A := ⟨A.1ᶜ, A.2.compl⟩
  compl_isComplement A :=
    ⟨Subtype.ext (Set.union_compl_self A.1), Subtype.ext (Set.inter_compl_self A.1)⟩
  sup_distrib A B C := Subtype.ext (Set.union_inter_distrib_left A.1 B.1 C.1)
  inf_distrib A B C := Subtype.ext (Set.inter_union_distrib_left A.1 B.1 C.1)

-- Lause 3.3.2: Stonen esityslause Boolen algebroille
def stonePhi (B : Type) [ThesisBooleanAlgebra B] : BooleanHom B (ClopenSet (Ult B)) where
  toFun b := ⟨stoneBasic b, stoneBasic_isClopen b⟩
  map_sup a b := Subtype.ext (stoneBasic_sup a b)
  map_inf a b := Subtype.ext (stoneBasic_inf a b)
  map_comp a {a'} ha := by
    have ha' : a' = aᶜ := ThesisBooleanAlgebra.compl_eq_of_isComplement ha
    subst ha'
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · change stoneBasic a ∪ stoneBasic (aᶜ) = Set.univ
      rw [← stoneBasic_sup, ThesisBooleanAlgebra.compl_sup, stoneBasic_top]
    · change stoneBasic a ∩ stoneBasic (aᶜ) = ∅
      rw [← stoneBasic_inf, ThesisBooleanAlgebra.compl_inf, stoneBasic_bot]

private lemma sep_ultrafilter_of_not_le {a b : B} (hnot : ¬(a ≤ b)) :
    ∃ U : Ult B, a ∈ U.carrier ∧ b ∉ U.carrier := by
  have hne : a ⊓ bᶜ ≠ (⊥ : B) := by
    intro hbot
    apply hnot
    have ha : a = a ⊓ b := by
      calc
        a = a ⊓ (⊤ : B) := (BoundedAlgebraicLattice.infId a).symm
        _ = a ⊓ (b ⊔ bᶜ) := by rw [ThesisBooleanAlgebra.compl_sup]
        _ = (a ⊓ b) ⊔ (a ⊓ bᶜ) := ThesisBooleanAlgebra.inf_distrib a b (bᶜ)
        _ = (a ⊓ b) ⊔ (⊥ : B) := by rw [hbot]
        _ = a ⊓ b := BoundedAlgebraicLattice.supId (a ⊓ b)
    exact (ord_iff_inf a b).mpr ha.symm
  let S : Set B := {a, bᶜ}
  have hS : S.Nonempty := ⟨a, Set.mem_insert a {bᶜ}⟩
  have hFIP : HasFIP B S := by
    intro T hT hT_bot
    have hle : a ⊓ bᶜ ≤ finsetInf B T := by
      clear hT_bot
      classical
      induction T using Finset.induction with
      | empty =>
        rw [finsetInf_empty]
        exact (ord_iff_sup (a ⊓ bᶜ) (⊤ : B)).mpr (BoundedAlgebraicLattice.supTop (a ⊓ bᶜ))
      | insert x s hx ih =>
        rw [finsetInf_insert_of_notMem B hx]
        apply OrderLattice.le_inf
        · rcases hT x (Finset.mem_insert_self x s) with hx_eq | hx_eq
          · rw [hx_eq]; exact OrderLattice.inf_le_left a (bᶜ)
          · rw [hx_eq]; exact OrderLattice.inf_le_right a (bᶜ)
        · exact ih (fun y hy ↦ hT y (Finset.mem_insert_of_mem hy))
    rw [hT_bot] at hle
    have hbot_le : (⊥ : B) ≤ a ⊓ bᶜ := by
      have haux : (⊥ : B) ⊓ (a ⊓ bᶜ) = (⊥ : B) := by
        rw [AlgebraicLattice.inf_comm]
        exact BoundedAlgebraicLattice.infBot (a ⊓ bᶜ)
      exact (ord_iff_inf (⊥ : B) (a ⊓ bᶜ)).mpr haux
    exact hne (ThesisPartialOrder.le_antisymm (a ⊓ bᶜ) (⊥ : B) hle hbot_le)
  have h_proper : (filtGen B S hS).IsProper :=
    (filtGen_isProper_iff_hasFIP B S hS).mpr hFIP
  rcases ultrafilter_exists (filtGen B S hS) h_proper with ⟨U, hU⟩
  have haU : a ∈ U.carrier := hU ⟨{a}, fun s hs ↦ by
    rw [Finset.mem_singleton.mp hs]; exact Set.mem_insert a {bᶜ},
    by rw [finsetInf_singleton]; exact ThesisPartialOrder.le_refl a⟩
  have hbcU : bᶜ ∈ U.carrier := hU ⟨{bᶜ}, fun s hs ↦ by
    rw [Finset.mem_singleton.mp hs]; exact Set.mem_insert_of_mem a rfl,
    by rw [finsetInf_singleton]; exact ThesisPartialOrder.le_refl (bᶜ)⟩
  exact ⟨U, haU, fun hbU ↦
    (ultrafilter_mem_iff_compl_notMem U b).mp hbU hbcU⟩

theorem stonePhi_injective : Function.Injective (stonePhi B) := by
  intro a b hab
  by_contra hne
  have h_not_le : ¬(a ≤ b) ∨ ¬(b ≤ a) := by
    by_contra h
    push Not at h
    exact hne (ThesisPartialOrder.le_antisymm a b h.1 h.2)
  have hset : stoneBasic a = stoneBasic b := congrArg Subtype.val hab
  rcases h_not_le with h | h
  · rcases sep_ultrafilter_of_not_le h with ⟨U, haU, hbU⟩
    have : U ∈ stoneBasic b := hset ▸ haU
    exact hbU this
  · rcases sep_ultrafilter_of_not_le h with ⟨U, hbU, haU⟩
    have : U ∈ stoneBasic a := hset.symm ▸ hbU
    exact haU this

private instance : Std.Commutative (fun (a b : B) => a ⊔ b) where
  comm := AlgebraicLattice.sup_comm

private instance : Std.Associative (fun (a b : B) => a ⊔ b) where
  assoc a b c := (AlgebraicLattice.sup_assoc a b c).symm

private def finsetSup (B : Type) [ThesisBooleanAlgebra B] (K : Finset B) : B :=
  K.fold (· ⊔ ·) (⊥ : B) id

private lemma stoneBasic_finsetSup (K : Finset B) :
    stoneBasic (finsetSup B K) = ⋃ b ∈ K, stoneBasic b := by
  classical
  induction K using Finset.induction with
  | empty =>
    simp [finsetSup, stoneBasic_bot]
  | insert a s ha ih =>
    rw [finsetSup, Finset.fold_insert ha]
    change stoneBasic (a ⊔ finsetSup B s) = _
    rw [stoneBasic_sup, ih, Finset.set_biUnion_insert]

theorem stonePhi_surjective : Function.Surjective (stonePhi B) := by
  classical
  intro A
  let I := {b : B // stoneBasic b ⊆ A.1}
  have h_cover : A.1 ⊆ ⋃ i : I, stoneBasic i.1 := by
    intro U hU
    rcases stoneBasis_isTopologicalBasis.isOpen_iff.mp A.2.isOpen U hU with
      ⟨_, ⟨b, rfl⟩, hbU, hb_sub⟩
    exact Set.mem_iUnion.mpr ⟨⟨b, hb_sub⟩, hbU⟩
  rcases A.2.isClosed.isCompact.elim_finite_subcover (fun i : I ↦ stoneBasic i.1)
      (fun i ↦ stoneBasic_isOpen i.1) h_cover with ⟨K, hK⟩
  let K' : Finset B := K.image Subtype.val
  refine ⟨finsetSup B K', Subtype.ext ?_⟩
  change stoneBasic (finsetSup B K') = A.1
  rw [stoneBasic_finsetSup]
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun b hb ↦ ?_
    rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
    exact i.2
  · intro U hU
    rcases Set.mem_iUnion₂.mp (hK hU) with ⟨i, hiK, hiU⟩
    exact Set.mem_iUnion₂.mpr ⟨i.1, Finset.mem_image_of_mem Subtype.val hiK, hiU⟩

theorem stone_representation : Function.Bijective (stonePhi B) :=
  ⟨stonePhi_injective, stonePhi_surjective⟩
