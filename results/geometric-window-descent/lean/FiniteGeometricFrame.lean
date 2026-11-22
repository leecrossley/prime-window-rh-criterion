import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
import FiniteSlopeShare

/-! The integrated rank-loss estimate of twinheterodox, applied to the
actual Hermitian lattices in Alpöge's archive by finite summation.
The rank comparison is used only at zero and the input slope thresholds. The filtration and rank
identifications below use the archived geometric comparison of TheoremFSharp. -/

open Module NumberField Finset Formalism.CorankShareLayerCake.FR
noncomputable section
namespace Formalism.HN

def FiniteFrameBound : Prop :=
  ∀ (K W κ κ₁ I : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁] [Fintype I] [Nonempty I]
    (V ι : I → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) W)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] W) (h : I → ℝ)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ) (γ : I → ℝ) (s u HH e η δ : ℝ),
    (∀ w, IsUnit (X' w).det) → (∀ i w, IsUnit (X i w).det) → (∀ i, IsUnit (Y i).det) →
    IsUnit Y'.det →
    cc.FG → Submodule.span K (cc : Set W) = ⊤ →
    (∀ i, (N i).FG) → (∀ i, Submodule.span K (N i : Set (V i)) = ⊤) →
    0 < ∑ i, Fintype.card (ι i) → (∀ i, (N i).map ((B i).restrictScalars (𝓞 K)) ≤ cc) →
    (∀ i, B i ≠ 0 → htMap (b i) (X i) b' X' (B i) ≤ h i) →
    s * (∑ i, (Fintype.card (ι i) : ℝ)) ≤
      ∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i) →
    0 ≤ u → (∀ i, muMaxDef (b i) (X i) (N i) - h i ≤ s + u) →
    s - muMinDef b' X' cc ≤ HH → 0 ≤ HH →
    0 ≤ δ → δ < 1 → (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (Fintype.card κ : ℝ) →
    (∀ i (k : κ) (j : ι i),
      Ball i (Sum.inl k) j = (Y'⁻¹ * (LinearMap.toMatrix (b i) b' (B i)).map v.embedding * Y i) k j) →
    (∀ i, 0 < γ i) →
    (∑ i, hs2 (frK (γ i) (Matrix.toEuclideanLin (Ball i)) - LinearMap.id)) ≤
      e * ∑ i, (Fintype.card (ι i) : ℝ) →
    0 ≤ e → e ≤ 1 / 4 →
    (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)) ∘ₗ
         frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ≤
      (1 + η) * (LinearMap.trace ℂ (EuclideanSpace ℂ (κ ⊕ κ₁))
        (frQ γ (fun i => Matrix.toEuclideanLin (Ball i)))).re ^ 2 /
        (Fintype.card (κ ⊕ κ₁) : ℝ) →
    0 ≤ η →
    s - (1 - δ)⁻¹ * (4 * (u * HH / (u + HH)) + (η + 4 * Real.sqrt e) * HH) ≤ muDef b' X' cc

set_option maxHeartbeats 4000000 in

theorem finite_frame_of (hLA : FrameLA1) : FiniteFrameBound := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax hHH hHH0
    hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  classical
  have : FiniteDimensional K W := Module.Finite.of_basis b'
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnR : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast hn
  have hδ' : 0 < 1 - δ := by linarith
  have hRR : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by exact_mod_cast hR

  have hD : 0 < Fintype.card κ := by
    by_contra hD0
    have hκ0 : Fintype.card κ = 0 := by omega
    have hall : (Fintype.card (κ ⊕ κ₁) : ℝ) = 0 := by
      have h1 : (1 - δ) * (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ 0 := by
        rw [hκ0, Nat.cast_zero] at hcard; exact hcard
      have h2 : (0:ℝ) ≤ (Fintype.card (κ ⊕ κ₁) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hemp : IsEmpty (κ ⊕ κ₁) := Fintype.card_eq_zero_iff.1 (by exact_mod_cast hall)
    have hz : ∀ i, Matrix.toEuclideanLin (Ball i) = 0 := by
      intro i; apply LinearMap.ext; intro x; ext k; exact isEmptyElim k
    have hF2' := hF2
    simp only [hz, hilbert_schmidt_zero_map, finrank_euclideanSpace] at hF2'
    nlinarith

  have hLN : ∀ i, IsLat (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) := fun i =>
    (place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (N i) (hNFG i)).1
  have hrkN : ∀ i, rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) =
      Module.finrank ℚ K * Fintype.card (ι i) := fun i => by
    rw [(place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (N i) (hNFG i)).2.1,
      frameB_rkK_top (b i) (N i) (hNSpan i)]
  have hLcc : IsLat (Formalism.HermitianLatticesTheory.realize b' X') cc := (place_lattice_structure K W κ b' X' hX' cc hccFG).1
  have hrkcc : rk (Formalism.HermitianLatticesTheory.realize b' X') cc = Module.finrank ℚ K * Fintype.card κ := by
    rw [(place_lattice_structure K W κ b' X' hX' cc hccFG).2.1, frameB_rkK_top b' cc hccSpan]
  have hNne : ∀ i, Fintype.card (ι i) ≠ 0 → N i ≠ ⊥ := by
    intro i hci h0
    have hc := frameB_rkK_top (b i) (N i) (hNSpan i)
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) (V i)) = 0 := by simp [rkK]
    omega
  have hccne : cc ≠ ⊥ := by
    intro h0
    have hc := frameB_rkK_top b' cc hccSpan
    rw [h0] at hc
    have h00 : rkK (⊥ : Submodule (𝓞 K) W) = 0 := by simp [rkK]
    omega

  let θ : ℝ → I → ℝ := fun τ i => (s - τ + h i - slopeNormalisingConstant K) / 2
  let Nt : ℝ → ∀ i, Submodule (𝓞 K) (V i) := fun τ i =>
    hnStep (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) (θ τ i)
  have hNtle : ∀ τ i, Nt τ i ≤ N i := fun τ i =>
    (frameB_hnStep _ _ _ _ _ (hLN i) (θ τ i)).1.1
  have hNtFG : ∀ τ i, (Nt τ i).FG := fun τ i => Submodule.FG.of_le (hNFG i) (hNtle τ i)
  have hrkNt : ∀ τ i, rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (Nt τ i) =
      Module.finrank ℚ K * rkK (Nt τ i) := fun τ i =>
    (place_lattice_structure K (V i) (ι i) (b i) (X i) (hX i) (Nt τ i) (hNtFG τ i)).2.1
  have hfilt (τ : ℝ) (i : I) : ((univ.filter (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j +
      slopeNormalisingConstant K - h i < s - τ)).card : ℝ) =
      (Module.finrank ℚ K : ℝ) * ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i)) := by
    rw [Finset.filter_congr (q := fun j => slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j < θ τ i)
      (fun j _ => by simp only [θ]; constructor <;> intro hj <;> linarith),
      frameB_count_lt _ (N i) (hLN i) (θ τ i)]
    change (rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (Nt τ i) = _
    rw [hrkN i, hrkNt τ i]
    push_cast; ring
  have input_mean : (∑ i, ((rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℕ) : ℝ)) * s ≤ ∑ i, ∑ j, (2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i) := by
    have hx : ∀ i, ∑ j, (2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K -
        h i) = (Module.finrank ℚ K : ℝ) *
        ((Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - h i)) := by
      intro i
      by_cases hci : Fintype.card (ι i) = 0
      · have h0 : rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
        have : IsEmpty (Fin (rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i))) := by
          rw [h0]; exact Fin.isEmpty'
        simp [hci]
      · simp_rw [add_sub_assoc]
        rw [frameB_sum_sl _ (N i) (hLN i)
            (by rw [hrkN i]; exact (Nat.mul_pos hn (Nat.pos_of_ne_zero hci)).ne'),
          hrkN i, frameB_muDef]
        push_cast; ring
    rw [Finset.sum_congr rfl fun i _ => hx i, ← Finset.mul_sum]
    simp only [hrkN]
    push_cast
    rw [← Finset.mul_sum, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hs) hnR.le
  have input_max : ∀ i j, 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i ≤ s+u := by
    intro i j
    by_cases hci : Fintype.card (ι i) = 0
    · exfalso
      have hj : (j : ℕ) < rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) := j.isLt
      have h0 : rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) = 0 := by rw [hrkN i, hci, mul_zero]
      omega
    · have hext := ((polygon_extreme_slopes _ _ _ _ (N i) (hLN i) (hNne i hci)).1 j).2
      have hm := hmax i
      rw [frameB_muMaxDef] at hm
      linarith


  let share (τ : ℝ) := (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i))) / (∑ i, (Fintype.card (ι i) : ℝ))
  have share_exact (τ : ℝ) : (∑ i, ((Fintype.card (ι i) : ℝ) - rkK (Nt τ i))) ≤ share τ * (∑ i, (Fintype.card (ι i) : ℝ)) := by
    dsimp [share]; rw [div_mul_cancel₀ _ hRR.ne']
  have share_nonneg (τ : ℝ) : 0 ≤ share τ := by
    apply div_nonneg _ hRR.le
    apply Finset.sum_nonneg
    intro i _
    have hc := Nat.cast_nonneg (α:=ℝ) ((univ.filter (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i < s-τ)).card)
    rw [hfilt τ i] at hc
    exact nonneg_of_mul_nonneg_right hc hnR
  have input_total : (∑ i, ((rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℕ) : ℝ)) = (Module.finrank ℚ K : ℝ) * (∑ i, (Fintype.card (ι i) : ℝ)) := by
    simp only [hrkN,Nat.cast_mul,Finset.mul_sum]
  have input_pos : 0 < (∑ i, ((rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℕ) : ℝ)) := by rw [input_total]; exact mul_pos hnR hRR
  have input_ratio (τ : ℝ) :
      (∑ i, ∑ j, if 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i<s-τ then (1:ℝ) else 0)/(∑ i, ((rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℕ) : ℝ)) = share τ := by
    simp only [Finset.sum_boole,hfilt,input_total,← Finset.mul_sum,share]
    field_simp [hnR.ne',hRR.ne']
  let θ' : ℝ → ℝ := fun τ => (s - τ - slopeNormalisingConstant K) / 2
  let St : ℝ → Submodule (𝓞 K) W := fun τ => hnStep (Formalism.HermitianLatticesTheory.realize b' X') cc (θ' τ)
  let M : ℝ → Submodule (𝓞 K) W := fun τ => ⨆ i, (Nt τ i).map ((B i).restrictScalars (𝓞 K))
  have hMle : ∀ τ, M τ ≤ St τ := by
    intro τ
    refine iSup_le fun i => ?_
    by_cases h0 : (Nt τ i).map ((B i).restrictScalars (𝓞 K)) = ⊥
    · rw [h0]; exact bot_le
    · have hBi : B i ≠ 0 := by
        intro hb; apply h0
        refine eq_bot_iff.2 ?_
        rintro _ ⟨y, _, rfl⟩
        simp [hb]
      have hNt0 : Nt τ i ≠ ⊥ := by
        intro h'; apply h0; rw [h']; exact Submodule.map_bot _
      have hsi := (slope_inequality_mean K (V i) (ι i) W κ (b i) (X i) b' X' (hX i) hX' (B i)
        (Nt τ i) (hNtFG τ i) h0).1
      have hst := (frameB_hnStep _ _ _ _ _ (hLN i) (θ τ i)).2.1 hNt0
      have hhi := hht i hBi
      refine (frameB_hnStep _ _ _ _ _ hLcc (θ' τ)).2.2.1 _ ?_ h0 ?_
      · exact le_trans (Submodule.map_mono (hNtle τ i)) (hBN i)
      · rw [frameB_muMinDef, frameB_muMinDef] at hsi
        simp only [θ, θ'] at hst ⊢
        linarith
  have hStle : ∀ τ, St τ ≤ cc := fun τ => (frameB_hnStep _ _ _ _ _ hLcc (θ' τ)).1.1
  have hStFG : ∀ τ, (St τ).FG := fun τ => Submodule.FG.of_le hccFG (hStle τ)
  have hrkSt : ∀ τ, rk (Formalism.HermitianLatticesTheory.realize b' X') (St τ) = Module.finrank ℚ K * rkK (St τ) :=
    fun τ => (place_lattice_structure K W κ b' X' hX' (St τ) (hStFG τ)).2.1
  have hrkM : ∀ τ, rkK (M τ) ≤ rkK (St τ) := fun τ =>
    Submodule.finrank_mono (Submodule.span_mono (SetLike.coe_subset_coe.2 (hMle τ)))

  let w : ℝ → ℝ := fun τ => (1 - δ)⁻¹ * (η + 4 * (share τ) + 4 * Real.sqrt e)
  have hplace : ∀ τ, (Fintype.card κ : ℝ) - rkK (M τ) ≤ w τ * Fintype.card κ := by
    intro τ
    have h1 := thmF_place hLA b' b B v Y Y' Ball γ e η (share τ) (Nt τ) hY hY' hγ hR hBall
      hF2 he0 he1 hη hF1 (share_exact τ)
    have hc0 : 0 ≤ η + 4 * (share τ) + 4 * Real.sqrt e := by
      have := share_nonneg τ
      have := Real.sqrt_nonneg e
      linarith
    have hA : (Fintype.card (κ ⊕ κ₁) : ℝ) ≤ (1 - δ)⁻¹ * Fintype.card κ := by
      rw [le_inv_mul_iff₀ hδ']; exact hcard
    have h2 := mul_le_mul_of_nonneg_left hA hc0
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = w τ * Fintype.card κ := by simp only [w]; ring

  have hcnt : ∀ τ ∈ Set.Icc (0 : ℝ) HH,
      ((univ.filter (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K < s - τ)).card : ℝ)
        ≤ w τ * (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℕ) := by
    intro τ _
    rw [Finset.filter_congr (q := fun j => slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j < θ' τ)
      (fun j _ => by simp only [θ']; constructor <;> intro hj <;> linarith),
      frameB_count_lt _ cc hLcc (θ' τ)]
    change (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) - rk (Formalism.HermitianLatticesTheory.realize b' X') (St τ) ≤ _
    rw [hrkcc, hrkSt τ]
    push_cast
    have h1 := hplace τ
    have h2 : (rkK (M τ) : ℝ) ≤ rkK (St τ) := by exact_mod_cast hrkM τ
    have h3 : (Fintype.card κ : ℝ) - rkK (St τ) ≤ w τ * Fintype.card κ := by linarith
    nlinarith
  have hlow : ∀ j, s - HH ≤ 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K := by
    intro j
    have hext := ((polygon_extreme_slopes _ _ _ _ cc hLcc hccne).1 j).1
    rw [frameB_muMinDef] at hHH
    linarith
  have hrkpos : 0 < rk (Formalism.HermitianLatticesTheory.realize b' X') cc := by rw [hrkcc]; exact Nat.mul_pos hn hD
  have hmean : (∑ j, (2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K)) /
      (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) = muDef b' X' cc := by
    rw [frameB_sum_sl _ cc hLcc hrkpos.ne', frameB_muDef]
    have : (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) ≠ 0 := by exact_mod_cast hrkpos.ne'
    field_simp
  have output_pos : (0:ℝ) < Fintype.card (Fin (rk (Formalism.HermitianLatticesTheory.realize b' X') cc)) := by
    rw [Fintype.card_fin]
    exact_mod_cast hrkpos
  have rank_bound (τ : ℝ) (hτ : τ ∈ Set.Icc (0:ℝ) HH) :
      ((1-δ)/(Fintype.card (Fin (rk (Formalism.HermitianLatticesTheory.realize b' X') cc)):ℝ))*(∑ j, if 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K < s-τ then (1:ℝ) else 0) ≤
        (η+4*Real.sqrt e)+(4/(∑ i, ((rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) : ℕ) : ℝ)))*(∑ i, ∑ j, if 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i < s-τ then (1:ℝ) else 0) := by
    have shape := hcnt τ hτ
    have target_pos : (0:ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b' X') cc : ℝ) := by exact_mod_cast hrkpos
    rw [Fintype.card_fin,Finset.sum_boole]
    calc _ ≤ ((1-δ)/(rk (Formalism.HermitianLatticesTheory.realize b' X') cc:ℝ))*(w τ*(rk (Formalism.HermitianLatticesTheory.realize b' X') cc:ℝ)) :=
               mul_le_mul_of_nonneg_left shape (div_nonneg hδ'.le target_pos.le)
         _ = (η+4*Real.sqrt e)+4*share τ := by
               dsimp [w]
               field_simp [hδ'.ne',target_pos.ne']
               ring
         _ = _ := by rw [←input_ratio τ]; ring
  have loss := FiniteSlopeShare.rank_share_transfer
    (fun i => rk (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i)) (fun i j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize (b i) (X i)) (N i) j + slopeNormalisingConstant K - h i) (fun j => 2 * slopeList (Formalism.HermitianLatticesTheory.realize b' X') cc j + slopeNormalisingConstant K) s u HH δ (η+4*Real.sqrt e)
    hu hHH0 hδ1 input_pos output_pos input_mean input_max hlow (fun τ hτ _ => rank_bound τ ⟨hτ.1,hτ.2.le⟩)
  simp only [Fintype.card_fin] at loss
  rw [hmean] at loss
  rw [show ((η+4*Real.sqrt e)*HH+4*(u*HH/(u+HH)))/(1-δ) =
    (1-δ)⁻¹*(4*(u*HH/(u+HH))+(η+4*Real.sqrt e)*HH) by ring] at loss
  linarith

private theorem harmonic_le_log {u h : ℝ} (hu : 0 ≤ u) (hh : 0 ≤ h) :
    u*h/(u+h) ≤ u*Real.log (1+h/u) := by
  rcases eq_or_lt_of_le hu with h0|up
  · subst u; simp
  have sum_pos : 0 < u+h := by linarith
  have one_pos : 0 < 1+h/u := by positivity
  have lower := Real.one_sub_inv_le_log_of_pos one_pos
  have eqn : u*h/(u+h) = u*(1-(1+h/u)⁻¹) := by field_simp [up.ne',sum_pos.ne']; ring
  rw [eqn]
  exact mul_le_mul_of_nonneg_left lower hu

/-- Retain the archived interface for existing callers, using the finite threshold proof. -/
theorem archive_frame_of_finite (strong : FiniteFrameBound) : TheoremFSharp := by
  intro K W κ κ₁ I _ _ _ _ _ _ _ _ _ _ _ _ _ _ V ι _ _ _ _ _ _ b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax hHH hHH0
    hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  have improved := strong K W κ κ₁ I V ι b' X' cc b X N B h v Y Y' Ball γ
    s u HH e η δ hX' hX hY hY' hccFG hccSpan hNFG hNSpan hR hBN hht hs hu hmax hHH hHH0
    hδ0 hδ1 hcard hBall hγ hF2 he0 he1 hF1 hη
  have le := harmonic_le_log hu hHH0
  have increase := mul_le_mul_of_nonneg_left
    (show 4*(u*HH/(u+HH)) + (η+4*Real.sqrt e)*HH ≤
      4*u*Real.log (1+HH/u) + (η+4*Real.sqrt e)*HH by linarith)
    (inv_nonneg.mpr (sub_nonneg.mpr hδ1.le))
  linarith

theorem finite_frame_compat_of (hLA : FrameLA1) : TheoremFSharp :=
  archive_frame_of_finite (finite_frame_of hLA)

#print axioms finite_frame_of
#print axioms finite_frame_compat_of

end Formalism.HN
