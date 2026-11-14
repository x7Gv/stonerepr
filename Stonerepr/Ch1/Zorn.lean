import Mathlib.Tactic

import Stonerepr.Ch1.Algebra
import Stonerepr.Ch1.Filter

variable {L : Type} [BoundedAlgebraicLattice L]
variable {B : Type} [ThesisBooleanAlgebra B]


@[ext]
lemma ThesisFilter.ext {B : Type} [BoundedAlgebraicLattice B] (F G : ThesisFilter B)
  (h : F.carrier = G.carrier) : F = G := by
  cases F
  cases G
  simp_all

-- Kytketään ThesisFilter Mathlibin järjestysteoriaan
instance {B : Type} [BoundedAlgebraicLattice B] : PartialOrder (ThesisFilter B) where
  le F G := F.carrier ⊆ G.carrier
  le_refl F := Set.Subset.refl F.carrier
  le_trans F G H hFG hGH := Set.Subset.trans hFG hGH
  le_antisymm F G hFG hGF := ThesisFilter.ext F G (Set.Subset.antisymm hFG hGF)

def ProperFiltersContaining (F : ThesisFilter B) : Set (Set B) :=
  {S | ∃ G : ThesisFilter B, G.carrier = S ∧ G.IsProper ∧ F.carrier ⊆ S}

lemma chain_union_is_proper (F : ThesisFilter B) (C : Set (Set B))
  (hC_sub : C ⊆ ProperFiltersContaining F)
  (hC_chain : IsChain (· ⊆ ·) C)
  (hC_nonempty : C.Nonempty) :
  ∃ C_star : ThesisFilter B, C_star.carrier = ⋃₀ C ∧ C_star.IsProper ∧ F.carrier ⊆ ⋃₀ C := by
    have h_is_filter :
        ∀ S ∈ C, ∃ G : ThesisFilter B, G.carrier = S ∧ G.IsProper ∧ F.carrier ⊆ S := hC_sub
    let C_star : ThesisFilter B := {
      carrier := ⋃₀ C
      top_mem := by
        rcases hC_nonempty with ⟨S, hS⟩
        rcases h_is_filter S hS with ⟨G, hG_eq, _, _⟩
        have htop : (⊤ : B) ∈ S := hG_eq ▸ G.top_mem
        exact Set.mem_sUnion_of_mem htop hS

      upwards_closed := by
        intro a b ha hab
        have hab_leq : a ≤ b := (ord_iff_sup a b).mpr hab
        rcases Set.mem_sUnion.mp ha with ⟨S, hS, has⟩
        rcases h_is_filter S hS with ⟨G, hG_eq, _, _⟩
        have h_a_in_G : a ∈ G.carrier := by
          rw [hG_eq]
          exact has
        have h_b_in_G : b ∈ G.carrier := G.upwards_closed a b h_a_in_G hab
        have hbs : b ∈ S := hG_eq ▸ h_b_in_G
        exact Set.mem_sUnion_of_mem hbs hS

      -- 3. Olkoot a, b ∈ C*. Tällöin a ∈ G1 ja b ∈ G2 joillakin G1, G2 ∈ C.
      -- Koska C on ketju, joko G1 ⊆ G2 tai G2 ⊆ G1.
      inf_mem := by
        intro a b ha hb
        rcases Set.mem_sUnion.mp ha with ⟨S1, hS1, has1⟩
        rcases Set.mem_sUnion.mp hb with ⟨S2, hS2, hbs2⟩
        rcases hC_chain.total hS1 hS2 with h12 | h21
        · -- Oletetaan (WLOG), että G1 ⊆ G2. Tällöin a, b ∈ G2...
          rcases h_is_filter S2 hS2 with ⟨G2, hG2_eq, _, _⟩
          have ha_S2 : a ∈ S2 := h12 has1
          have ha_G2 : a ∈ G2.carrier := by
            rw [hG2_eq]
            exact ha_S2
          have hb_G2 : b ∈ G2.carrier := by
            rw [hG2_eq]
            exact hbs2
          have hab_G2 : a ⊓ b ∈ G2.carrier := G2.inf_mem a b ha_G2 hb_G2
          have hab_S2 : a ⊓ b ∈ S2 := hG2_eq ▸ hab_G2
          exact Set.mem_sUnion_of_mem hab_S2 hS2
        · -- Symmetrinen tapaus G2 ⊆ G1
          rcases h_is_filter S1 hS1 with ⟨G1, hG1_eq, _, _⟩
          have hb_S1 : b ∈ S1 := h21 hbs2
          have ha_G1 : a ∈ G1.carrier := by
            rw [hG1_eq]
            exact has1
          have hb_G1 : b ∈ G1.carrier := by
            rw [hG1_eq]
            exact hb_S1
          have hab_G1 : a ⊓ b ∈ G1.carrier := G1.inf_mem a b ha_G1 hb_G1
          have hab_S1 : a ⊓ b ∈ S1 := hG1_eq ▸ hab_G1
          exact Set.mem_sUnion_of_mem hab_S1 hS1
    }
    use C_star
    refine ⟨rfl, ?_, ?_⟩
    · -- 4. Filtteri C* on aito, koska jos ⊥ ∈ C*, niin ⊥ ∈ G...
      intro h_univ
      have hbot : (⊥ : B) ∈ C_star.carrier := h_univ.symm ▸ Set.mem_univ (⊥ : B)
      rcases Set.mem_sUnion.mp hbot with ⟨S, hS, hbot_S⟩
      rcases h_is_filter S hS with ⟨G, hG_eq, hG_proper, _⟩
      have hbot_G : (⊥ : B) ∈ G.carrier := by
        rw [hG_eq]
        exact hbot_S
      have hG_univ : G.carrier = Set.univ := filter_univ_of_bot_mem G hbot_G
      exact hG_proper hG_univ
    · -- Selvästi F ⊆ C*
      rcases hC_nonempty with ⟨S, hS⟩
      rcases h_is_filter S hS with ⟨_, _, _, hF_sub_S⟩
      exact Set.Subset.trans hF_sub_S (Set.subset_sUnion_of_mem hS)

-- Lause 2.4.3 (Ultrafiltterilause)
theorem ultrafilter_exists (F : ThesisFilter B) (hF : F.IsProper) :
  ∃ U : ThesisUltrafilter B, F.carrier ⊆ U.carrier := by
  -- Kokoelma 𝓕 = ProperFiltersContaining F
  let 𝓕 := ProperFiltersContaining F
  -- Sovelletaan Zornin lemmaa joukkoon 𝓕
  have hzorn := zorn_subset 𝓕 (by
    intro C hC_sub hC_chain
    -- Tarkistetaan ylärajan olemassaolo: onko ketju tyhjä vai epätyhjä?
    rcases C.eq_empty_or_nonempty with rfl | hC_nonempty
    · -- Jos ketju on tyhjä, F itse on triviaalisti yläraja
      use F.carrier
      refine ⟨?_, by simp⟩
      use F
    · -- Ketju on epätyhjä, osoitetaan että C* = ⋃ C on yläraja kokoelmassa 𝓕
      use ⋃₀ C
      have ⟨C_star, hC_eq, hC_proper, hF_sub_C⟩ :=
        chain_union_is_proper F C hC_sub hC_chain hC_nonempty
      refine ⟨?_, fun S hS ↦ Set.subset_sUnion_of_mem hS⟩
      use C_star
  )
  -- Zornin lemma 2.4.2 antaa maksimaalisen alkion U joukosta 𝓕
  rcases hzorn with ⟨U_carrier, ⟨G, hG_eq, hG_proper, hF_sub_U⟩, hMax⟩
  -- Osoitetaan, että tämä maksimaalinen aito filtteri G on ultrafiltteri
  let U : ThesisUltrafilter B := {
    toThesisFilter := G
    proper := hG_proper
    maximal := by
      intro U' hG_sub_U'
      -- Jos U' on aito filtteri, joka sisältää G:n...
      by_cases hU'_proper : U'.carrier = Set.univ
      · exact Or.inl hU'_proper
      · right
        -- ...niin se sisältyy kokoelmaan 𝓕 ...
        have hU'_in_𝓕 : U'.carrier ∈ 𝓕 := by
          use U'
          exact ⟨rfl, hU'_proper, Set.Subset.trans (by
            exact le_of_le_of_eq hF_sub_U (id (Eq.symm hG_eq))
          ) hG_sub_U'⟩
        have hU_sub_U' : U_carrier ⊆ U'.carrier := by
          exact le_of_eq_of_le (id (Eq.symm hG_eq)) hG_sub_U'
        -- ... jolloin inkluusion suhteen maksimaalisuudesta (hMax) seuraa U' = G.
        have h_eq : U'.carrier = U_carrier :=
          Set.Subset.antisymm (hMax hU'_in_𝓕 hU_sub_U') hU_sub_U'
        exact hG_eq ▸ h_eq
  }
  use U
  exact le_of_le_of_eq hF_sub_U (id (Eq.symm hG_eq))
