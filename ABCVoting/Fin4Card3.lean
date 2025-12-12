import ABCVoting.Basic

open Finset

namespace ABCVoting

lemma fin4_card3_mem_zero (s : Finset (Fin 4)) (hs : s.card = 3) (h0 : (0 : Fin 4) ∈ s) :
    s = ({0, 1, 2} : Finset (Fin 4)) ∨
    s = ({0, 2, 3} : Finset (Fin 4)) ∨
    s = ({0, 1, 3} : Finset (Fin 4)) := by
  classical
  have hcompl : sᶜ.card = 1 := by
    simpa [hs, Fintype.card_fin] using (Finset.card_compl (s := s))
  rcases Finset.card_eq_one.mp hcompl with ⟨m, hm⟩
  have hm0 : m ≠ (0 : Fin 4) := by
    intro h
    have : (0 : Fin 4) ∈ sᶜ := by simpa [hm, h]
    exact (Finset.mem_compl.mp this) h0
  have hs' : s = Finset.univ.erase m := by
    calc
      s = (sᶜ)ᶜ := by simpa using (Finset.compl_compl (s := s)).symm
      _ = ({m} : Finset (Fin 4))ᶜ := by simpa [hm]
      _ = Finset.univ.erase m := by
        ext x
        simp
  fin_cases m
  · cases hm0 rfl
  · right; left
    have : (Finset.univ.erase (1 : Fin 4)) = ({0, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · right; right
    have : (Finset.univ.erase (2 : Fin 4)) = ({0, 1, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · left
    have : (Finset.univ.erase (3 : Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this

lemma fin4_card3_mem_one (s : Finset (Fin 4)) (hs : s.card = 3) (h1 : (1 : Fin 4) ∈ s) :
    s = ({0, 1, 2} : Finset (Fin 4)) ∨
    s = ({0, 1, 3} : Finset (Fin 4)) ∨
    s = ({1, 2, 3} : Finset (Fin 4)) := by
  classical
  have hcompl : sᶜ.card = 1 := by
    simpa [hs, Fintype.card_fin] using (Finset.card_compl (s := s))
  rcases Finset.card_eq_one.mp hcompl with ⟨m, hm⟩
  have hm1 : m ≠ (1 : Fin 4) := by
    intro h
    have : (1 : Fin 4) ∈ sᶜ := by simpa [hm, h]
    exact (Finset.mem_compl.mp this) h1
  have hs' : s = Finset.univ.erase m := by
    calc
      s = (sᶜ)ᶜ := by simpa using (Finset.compl_compl (s := s)).symm
      _ = ({m} : Finset (Fin 4))ᶜ := by simpa [hm]
      _ = Finset.univ.erase m := by
        ext x
        simp
  fin_cases m
  · right; right
    have : (Finset.univ.erase (0 : Fin 4)) = ({1, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · cases hm1 rfl
  · right; left
    have : (Finset.univ.erase (2 : Fin 4)) = ({0, 1, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · left
    have : (Finset.univ.erase (3 : Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this

lemma fin4_card3_mem_two (s : Finset (Fin 4)) (hs : s.card = 3) (h2 : (2 : Fin 4) ∈ s) :
    s = ({0, 1, 2} : Finset (Fin 4)) ∨
    s = ({0, 2, 3} : Finset (Fin 4)) ∨
    s = ({1, 2, 3} : Finset (Fin 4)) := by
  classical
  have hcompl : sᶜ.card = 1 := by
    simpa [hs, Fintype.card_fin] using (Finset.card_compl (s := s))
  rcases Finset.card_eq_one.mp hcompl with ⟨m, hm⟩
  have hm2 : m ≠ (2 : Fin 4) := by
    intro h
    have : (2 : Fin 4) ∈ sᶜ := by simpa [hm, h]
    exact (Finset.mem_compl.mp this) h2
  have hs' : s = Finset.univ.erase m := by
    calc
      s = (sᶜ)ᶜ := by simpa using (Finset.compl_compl (s := s)).symm
      _ = ({m} : Finset (Fin 4))ᶜ := by simpa [hm]
      _ = Finset.univ.erase m := by
        ext x
        simp
  fin_cases m
  · right; right
    have : (Finset.univ.erase (0 : Fin 4)) = ({1, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · right; left
    have : (Finset.univ.erase (1 : Fin 4)) = ({0, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · cases hm2 rfl
  · left
    have : (Finset.univ.erase (3 : Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this

lemma fin4_card3_mem_three (s : Finset (Fin 4)) (hs : s.card = 3) (h3 : (3 : Fin 4) ∈ s) :
    s = ({0, 1, 3} : Finset (Fin 4)) ∨
    s = ({0, 2, 3} : Finset (Fin 4)) ∨
    s = ({1, 2, 3} : Finset (Fin 4)) := by
  classical
  have hcompl : sᶜ.card = 1 := by
    simpa [hs, Fintype.card_fin] using (Finset.card_compl (s := s))
  rcases Finset.card_eq_one.mp hcompl with ⟨m, hm⟩
  have hm3 : m ≠ (3 : Fin 4) := by
    intro h
    have : (3 : Fin 4) ∈ sᶜ := by simpa [hm, h]
    exact (Finset.mem_compl.mp this) h3
  have hs' : s = Finset.univ.erase m := by
    calc
      s = (sᶜ)ᶜ := by simpa using (Finset.compl_compl (s := s)).symm
      _ = ({m} : Finset (Fin 4))ᶜ := by simpa [hm]
      _ = Finset.univ.erase m := by
        ext x
        simp
  fin_cases m
  · right; right
    have : (Finset.univ.erase (0 : Fin 4)) = ({1, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · right; left
    have : (Finset.univ.erase (1 : Fin 4)) = ({0, 2, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · left
    have : (Finset.univ.erase (2 : Fin 4)) = ({0, 1, 3} : Finset (Fin 4)) := by
      decide
    simpa [hs'] using this
  · cases hm3 rfl

end ABCVoting
