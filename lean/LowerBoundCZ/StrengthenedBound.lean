import LowerBoundCZ.MandatoryPrefix

/-! The final endpoint polynomial closes the full physical ledger.
Only fixed finite certificate checks are external; no physical slack,
traversal, endpoint inequality or lower bound is supplied by the caller. -/
noncomputable section
namespace LowerBoundCZ.Certification.Strengthened
open CZExposure MvPolynomial TerminalCertificate OccupationLedger

def ratio : ℝ := (SlackData.bound - MandatoryPrefix.base) /
  (right 320 - MandatoryPrefix.base)
def endpointPolynomial : UniPoly :=
  aeval (fun _ : Unit => C ratio * X ()) MandatoryPrefix.endpointPolynomial +
    C ((totalCredit : ℝ) - MandatoryPrefix.credit + right 320 - SlackData.bound)
def bernsteinPolynomial : UniPoly :=
  ∑ k : Fin 14, C (SlackData.endpoint k : ℝ) * C (Nat.choose 13 k.val : ℝ) *
    X ()^k.val * (1-X ())^(13-k.val)

/-- One fixed degree-13 coefficient identity; no trajectory quantifier. -/
def EndpointCheck : Prop := endpointPolynomial = bernsteinPolynomial

theorem endpoint_value (h : MandatoryPrefix.EndpointChecks) (γ : ActivePulse) :
    eval (fun _ => (γ.exposure-MandatoryPrefix.base)/(SlackData.bound-MandatoryPrefix.base))
      endpointPolynomial =
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) - evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) +
      (totalCredit : ℝ) + (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) - (SlackData.bound : ℝ) := by
  have hn : (SlackData.bound : ℝ) - MandatoryPrefix.base ≠ 0 := by
    norm_num [SlackData.bound, MandatoryPrefix.base]
  have hx : ratio * ((γ.exposure-MandatoryPrefix.base)/(SlackData.bound-MandatoryPrefix.base)) =
      (γ.exposure-MandatoryPrefix.base)/(right 320-MandatoryPrefix.base) := by
    unfold ratio; field_simp
  have hs (p : UniPoly) :
      eval (fun _ => (γ.exposure-MandatoryPrefix.base)/(SlackData.bound-MandatoryPrefix.base))
        (aeval (fun _ : Unit => C ratio * X ()) p) =
      eval (fun _ => (γ.exposure-MandatoryPrefix.base)/(right 320-MandatoryPrefix.base)) p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, eval_C, hp, hx]
  simp only [endpointPolynomial, map_add, eval_C, hs, MandatoryPrefix.endpoint_value h γ]
  ring

theorem endpoint_matches (h : EndpointCheck) (t : ℝ) :
    eval (fun _ => t) endpointPolynomial = Slack.endpoint.eval₂ (Rat.castHom ℝ) t := by
  rw [h]
  simp [bernsteinPolynomial, Slack.endpoint, Slack.bernsteinSum, _root_.bernsteinPolynomial,
    Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_sub, mul_assoc]

theorem pulse_lower (hl : MandatoryPrefix.LayoutChecks) (hb : MandatoryPrefix.EndpointChecks)
    (hf : EndpointCheck) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) (γ : ActivePulse) :
    (SlackData.bound : ℝ) < γ.exposure := by
  by_contra hn
  have hB : γ.exposure ≤ (SlackData.bound : ℝ) := le_of_not_gt hn
  have hcap : γ.exposure ≤ 733/250 := hB.trans Slack.bound_values.2.2.le
  have hL : (Slack.base : ℝ) ≤ γ.exposure := by
    have h := EReal.coe_le_coe_iff.mp
      ((Pinned.order7_checks_of_grams A hm).active_lower.trans (iInf_le _ γ))
    simpa only [Pinned.order7, Slack.base, Rat.cast_div, Rat.cast_ofNat] using h
  have ht := MandatoryPrefix.credited_telescope hl hb hc ha hr A hm hi hcap
  have he := endpoint_value hb γ
  rw [endpoint_matches hf] at he
  apply Slack.endpoint_excludes hL hB
  change (SlackData.bound : ℝ) - MandatoryPrefix.base +
    Slack.endpoint.eval₂ (Rat.castHom ℝ)
      ((γ.exposure-MandatoryPrefix.base)/(SlackData.bound-MandatoryPrefix.base)) ≤
    γ.exposure-MandatoryPrefix.base
  linarith

/-- Infima preserve the non-strict bound, not necessarily the strict
pointwise bound: no claim that the infimum is attained is needed. -/
theorem active_lower (hl : MandatoryPrefix.LayoutChecks) (hb : MandatoryPrefix.EndpointChecks)
    (hf : EndpointCheck) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) :
    ((SlackData.bound : ℝ) : EReal) ≤ activeCstar := by
  exact le_iInf fun γ => EReal.coe_le_coe_iff.mpr (pulse_lower hl hb hf hc ha hr A hm hi γ).le

theorem lab_lower (hl : MandatoryPrefix.LayoutChecks) (hb : MandatoryPrefix.EndpointChecks)
    (hf : EndpointCheck) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) :
    ((SlackData.bound : ℝ) : EReal) ≤ labCstar := by
  rw [labCstar_eq_activeCstar]
  exact active_lower hl hb hf hc ha hr A hm hi

theorem lab_window (hl : MandatoryPrefix.LayoutChecks) (hb : MandatoryPrefix.EndpointChecks)
    (hf : EndpointCheck) (hc : OccupationCoverage.DataChecks)
    (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (A : GramBridge.Archive Pinned.order7) (hm : GramBridge.MatrixChecks A)
    (hi : PinnedInterface.NumericalChecks) (hu : Pinned.UpperChecks) :
    ((SlackData.bound : ℝ) : EReal) ≤ labCstar ∧
      labCstar < (LowerBoundCZ.upperEndpoint : EReal) :=
  ⟨lab_lower hl hb hf hc ha hr A hm hi, Pinned.upper_lab_bound hu⟩

end LowerBoundCZ.Certification.Strengthened
