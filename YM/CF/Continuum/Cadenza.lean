import YM.CF.Continuum.Aurora
import YM.CF.Continuum.CityGate
import YM.CF.Continuum.Target

/-! # Cost loans for a depth-independent conditioning ratio test

 Positive here means *nonzero magnitude*; not claiming probability positivity
 for the gauge mask. Won't assume sign cancellations. Receipts align units
 so can use ratios at the UV-limit, THEN choose pivot. (These estimates are
 for normalized torus bottom-level observations, not a level-consistency
 extension of the product nor the infinite-volume signature.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function MeasureTheory NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Dial Peaks Scree Skye Emu Graph Cascade Vault Paige Nova Mint Mint.Roe
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8192
variable {L B N m:Side}{j n:ℕ}{r d c k x κ b t a e q s y y' v A L':ℝ}{O:Odd L.val}{Y:Pricing j L O (Thread j)} {P:Grasp Y B d}{hP:Pearl P}
variable (D:Pic.Span hP κ b x c t r n)

-- physical wing polarities: H.two controls cost.
abbrev pawIdx := Fin 2 × Fin 2
abbrev pawTag (g:Fin 3)(s:pawIdx) := index (lesser g) s.1 s.2
abbrev pawCurrent (g:Fin 3)(i:pawIdx)(s:Site N):=glowRead (some (pawTag g i)) s
lemma in_up (a:SpinIdx)(p:a∈plusHalf) : ∃ i,upSpin i=a:=by fin_cases a <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact absurd p (by decide)
lemma in_dn (a:SpinIdx)(p:a∉plusHalf) : ∃ i,dnSpin i=a:=by fin_cases a <;> first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact absurd p (by decide)
lemma has_beat(j:ℕ)(h:1≤j): ∀ y:ℝ, 0≤y→ ∃ k:ℕ,∀ N:Side,k≤N.val→Even N.val→∀ g:Fin 3,∀ M:Jill.Male,∃ i:pawIdx, y< ‖bias g M j N (pawTag g i).down (pawTag g i).up‖:=by
 intro y u; obtain ⟨c,C,hc,hC,k,f⟩:= growsTilt j h; obtain ⟨i,ht⟩:= exists_nat_gt (4*y/c)
 refine ⟨max k i,fun N e p g M=>?_⟩; let n:ℝ:= N.val; let Q:=bias g M j N; have he:1≤n:=Nat.one_le_cast.mpr N.property; obtain ⟨a,b⟩:=max_le_iff.mp e; have hx:4*y < ‖Q‖:=by
    have h:4*y/c<n:=ht.trans_le (Nat.cast_le.mpr b); rw [div_lt_iff₀ hc] at h; refine lt_of_lt_of_le h (le_trans ?_ (f N a p g M).1); rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by nlinarith [pow_le_pow_right₀ he (show 1 ≤ 5 by decide)]) hc.le
 by_contra! v; apply not_le.mpr hx; change ‖Q‖≤(Fintype.card SpinIdx:ℝ)*y -- tune defeq
 refine cost_D Q ?_ u; intro i s
 by_cases hi:i∈plusHalf
 · have hr:Q i s=0:=(biasMoney g M h p s i (dnSpin 0) hi (dn_half 0)).1; rwa [hr,norm_zero]
 by_cases hs:s∈plusHalf
 · obtain ⟨i',rfl⟩:= in_dn i hi; obtain ⟨t',rfl⟩:= in_up s hs; exact v (t',i')
 have hr:Q i s=0:=(biasMoney g M h p i (upSpin 0) s (up_half 0) hs).2; rwa [hr,norm_zero]
local notation "Λ" => CSide m B
include D
lemma tilt_leg (V:GramM (mid m B))(hv:n≤ (CSide m B).val)(g:Fin 3)(i:pawIdx)(s:Site Λ) : comparedToTilt (some (pawTag g i)) V s q P= normalizedTilt P q V * bias g V.J.M j Λ (pawTag g i).down (pawTag g i).up:=by
 obtain ⟨p,z⟩:= D.plan m hv; let U:=Kea.tax (N:=Domain m B) (needles Λ); let M:=V.J.M; unfold comparedToTilt glowRead; let F:=field (needlesView Λ) j M; let Y:=changeM (m:=m) P U M; have he:Sea (Dofu Λ F) Y:=by rw [show Dofu Λ F= _ from (z.2 (needles Λ) _ M).symm]; exact sea_g p _ (tax_guard _ _ _ D.eP.le) _
 rw [show Option.elim _ _ _=_ from (show glowRead (some (pawTag g i)) s=current Λ (lesser g) s _ _ from rfl)]; change yieldAngle V q • oneField 1 Y (current Λ (lesser g) s (upSpin i.1) (dnSpin i.2))= _; rw [shiftLaw g _ D.p z.1 s _ _ (up_half i.1) (dn_half i.2) _ he, ← Algebra.smul_mul_assoc,oneField_vac]; rfl

-- export certificate independent of projection phase; doesn't require limits of V.J.M.
structure Tango (m:Side)(B:Side)(K:Evaluation (CSide m B)→ℂ)(q y v:ℝ) : Prop where
 pace : y ≤ ‖K (compass (CSide m B) q)‖
 heart(g:Fin 3)(s:Site (CSide m B)) : ∃ i:pawIdx, ‖K (compass (CSide m B) q)‖*v ≤ ‖K (compass (CSide m B) q * pawCurrent g i s)‖

variable (V:GramM (mid m B))(W:Loom (mid m B))
set_option maxHeartbeats 400000
local notation "βΩ" => ‖normalizedTilt P q V‖ -- econ
lemma tango_cost (H:Tableau m V W P s a)(hz:y' ≤ ‖normalizedTilt P q V‖)(H1:∀ F s,‖moment (recX P V W) (compass (CSide m B) q*glowRead F s)-comparedToTilt F V s q P‖ ≤ 1/2* ‖normalizedTilt P q V‖)
   (hs:∀ g:Fin 3,∀ M:Jill.Male,∃ i:pawIdx, 2*v+1< ‖bias g M j (CSide m B) (pawTag g i).down (pawTag g i).up‖)(he:n≤ (CSide m B).val)(vP:0<v)(hy:0≤y') : Tango m B (finiteForm Y P V W) q (y'/2/Real.exp (budgetCharge V s a)) v:=by
 let Z:=Complex.exp (-V.v)*partitionZ V P W; let A:=compass Λ q; let N:=normalizedTilt P q V; have ht:0 < ‖Z‖:= (Real.exp_pos _).trans_le H.lowB; let k(U:Evaluation Λ):= moment (recX P V W) U; have hv: ‖k A-N‖≤ 1/2*‖N‖:=by have t:=H1 (none:GlowLeg) 0; rw [tilt_start,show glowRead none (0:Site Λ)=1 from rfl, mul_one] at t; exact t
 constructor
 · rw [relative (m:=m),norm_div]; refine le_trans ?_ ((div_le_div_of_nonneg_right (show y'/2 ≤ ‖k A‖ from ?_) ht.le)); · exact div_le_div_of_nonneg_left (by positivity) ht ((price_vs V W H.isPay).trans H.highB)
   have hg : ‖N‖ ≤ ‖k A‖+1/2*‖N‖ :=by calc
     _ ≤ ‖k A‖+‖k A-N‖:= by nth_rw 1 [← show k A- (k A-N)=N by abel]; exact norm_sub_le ..
     _ ≤ _:= add_le_add_right hv _ -- tune left
   linarith
 intro g x'; obtain ⟨i,he'⟩:=hs g V.J.M; let K:= A*pawCurrent g i x'; let B1:=bias g V.J.M j Λ (pawTag g i).down (pawTag g i).up; refine ⟨i, ?_⟩; simp_rw [relative (m:=m),norm_div]; change ‖k A‖/‖Z‖* _ ≤ ‖k K‖/ ‖Z‖; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ ht.le; have hl := H1 (some (pawTag g i)) x'; rw [tilt_leg D V he g] at hl; change ‖k K-N*B1‖≤1/2*‖N‖ at hl
 have hp:‖k A‖ ≤ ‖N‖+1/2*‖N‖:=by have g:= norm_add_le (k A-N) N; rw [sub_add_cancel] at g; linarith
 have hh: ‖N‖*‖B1‖≤ ‖k K‖+1/2*‖N‖:=by have g:= norm_sub_le (k K) (k K-N*B1); rw [show k K-(k K-N*B1)=N*B1 by abel,norm_mul] at g; linarith
 change 2*v+1<‖B1‖ at he'; nlinarith only [show ‖N‖*(2*v+1) ≤ ‖N‖*‖B1‖ from mul_le_mul_of_nonneg_left he'.le (norm_nonneg _), mul_le_mul_of_nonneg_right hp vP.le, hh,vP,norm_nonneg N]
end YM.CF.Window
