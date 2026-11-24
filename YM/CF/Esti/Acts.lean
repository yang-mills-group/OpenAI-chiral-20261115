import YM.CF.Esti.Snow
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {T:Tube G S}{E D:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup D][NormedSpace ℝ D]{V:E→ Config G c}{U:E→ Config G f}{F':Tree.Forest S.ratio}{k:S.Choices}{q:Chi}{u:E}
private lemma skip_le {α:Type}[Fintype α](g:α→E→D)(p:∀ i, Allows n (g i) u C): Allows n (fun y=>∑ i,g i y) u (Fintype.card α*C):=by simpa only [sum_const,card_univ,nsmul_eq_mul] using Jet.allows_sum (s:=Finset.univ) (fun i _=>p i)
lemma minus_e{g f:E→D}(h:Allows n f u C)(p:Allows n g u K):Allows n (fun y=>f y-g y) u (C+K):=by have he:=h.add (p.smul (-1)); simpa only [neg_one_smul,abs_neg,abs_one,one_mul,←sub_eq_add_neg] using he
abbrev murP (n:ℕ)(p:Clip)(C:ℝ):= max (4*(p.linear+p.direct)) (p.direct * Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C))
open Pressure.Tube Bloch Exterior
-- paid bound with hold.J
structure Circus (T:Tube G S)(s v:ℝ)(P: Finset (Cell f))(Q:Finset (Cell c))(U:E→ Config G f)(V:E→ Config G c)(M:E → Bond c→ SU.group.Mat)(u:E)(r n:ℕ)(x:ℝ):Prop where
 L1(i): Allows n (fun y=>kF T r s v P Q (V y) (U y) i) u x
 L2(i): Allows n (fun y=>kI T r v Q (V y) (M y) i) u x
 L3(i): Allows n (fun y=> kC T r v Q (V y) i+(kL T r v Q (V y) (U y) (M y) i+kD T r v Q (V y) i)) u x
 L4(i): Allows n (fun y=> kN T r v Q (V y) i) u x
lemma scope_p (K:Teller G)(P:Patch)(s:ℝ) (v C:ℝ)(hv:0 ≤ v)(h:‖(1:SU.group.Mat)‖ ≤ C)(n:ℕ)(p:Push.Uniform.PaintSupply G n s): ∃ L:ℝ,0 ≤ L ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{c f:Side}(S:StepData c f)(T:Tube G S),S.patch=P→ K.Funds S T→ ∀ (U:E→ Config G f)(V:E→ Config G c)(M:E→Bond c→SU.group.Mat)(u:E)(X: Finset (Cell c))(F:Finset (Cell f))(r:ℕ), (∀ i, Allows n (fun v=>M v i) u v)→ HeldT U F u→ HeldT V X u→ FuelG E V u n C→ FuelG E U u n C →∀ (x y:ℝ),x∈Set.Icc (0:ℝ) 1→y∈Set.Icc (0:ℝ) 1→ Circus T x y F X U V M u r n L :=by
 have he:0≤ C:=(norm_nonneg _).trans h
 obtain ⟨f,d,hf,hd,Hf⟩:= shortened K.top.clip K.top.paths K.top.width_pos p he; obtain ⟨c,e,hc,ht,Hc⟩:=shortened K.below.clip K.below.paths K.below.width_pos p he
 obtain ⟨Q,hQ,H⟩:= avoids K P.L C h n; let B:=Q*c; have hB:0≤ B:=mul_nonneg hQ.le hc.le; let t:=Real.sqrt K.bind.penalty * (curvatureCost G*v); let b:=Push.Uniform.priceCost G v; let D:= (2:ℝ)^n; let A:=Fintype.card Bool; let P₁:= murP n K.top.clip C; let P₂:=murP n K.below.clip C
 let F:=P₁ +D*f*f + A*(D*B*B+D*B*f); let C':=A*(D*c*c+D*c*c)+(P₂+D*c*c); let L:= A*(D*c*(Q*f + Q*t+c)); let N:=D*B*B; let W:= K.bind.penalty*b + (D*B*B+D*B*t); let X:=(A:ℝ)*(1/2*(D*c*(c+(Q*B+Q*B+Q*B)))); let X':=C'+(L+X); let R:=max 0 (max (max F N) (max W X'))
 refine ⟨R,le_max_left ..,@fun E _ _ g u S T hp hU U V M x Ω P' r hM θ p' Hx E' s t' hX hY=>?_⟩
 obtain ⟨M',M₀,hr,hg⟩:=hU.feeds; have ht':K.top.clip=T.high:=hU.high.symm; have hl':K.below.clip=T.low:=hU.low.symm; have ht(X:Twin _): Allows n (fun y=>T.Xf r (U y) X) x f:=by unfold Xf; rw [←ht']; exact Hf U _ E' T.up hr _ _ (by decide) _
 have hl(X:Twin _): Allows n (fun y=>T.Xn r (V y) X) x c:=by unfold Xn; rw [←hl']; exact Hc V _ Hx _ hg _ _ S.patch.L.property _
 have he(j): Allows n (fun y=>wV T r t' Ω (V y) j) x c:=pruned p' _ hc.le _ hY.1 _ _ _ _ _ (hl j); obtain ⟨Q₁,Q₂,Q₃⟩:= H V x Hx S (congr_arg _ hp) T hU r -- check eq
 have hf1(j):=creek j T.high s hX.1 hX.2 E' _ θ; have hk(j): Allows n (fun y=>kZ (S:=S) (M y) j) x t:=by unfold kZ; rw [hU.knobs]; exact ((arc_b  (hM j)).smul _).mono (le_of_eq (by rw [abs_of_nonneg (Real.sqrt_nonneg ..)])) -- tune name G parser
 have hb :=Q₁.1 _ _ hc.le he; have hh:=Q₂.1 _ _ hc.le he; have ha :0≤ t:=mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (curvature_nn _) hv)
 have hpP:max (max F N) (max W X') ≤ R:=le_max_right ..; refine ⟨fun i=> Allows.mono (C:=F) ?_ ((le_max_left ..).trans ((le_max_left ..).trans hpP)),fun i=> ?_,fun i=> ?_,fun i=>?_⟩
 · have hp : Allows n (fun v=>hallP P' T.high (U v) i s) x P₁:= (hf1 i).mono (le_of_eq (by unfold P₁ murP; rw [ht'])) -- args
   exact (hp.add (cow (pruned θ f hf.le _ hX.1 _ _ _ _ _ (ht _)))).add (skip_le _ fun j:Bool=>minus_e (cow (hb (i,j))) (bia (hb (i,j)) (ht (i,j))))
 · refine Allows.mono (C:=W) ?_ ((le_max_left ..).trans ((le_max_right ..).trans hpP)); have hφ:Allows n (fun v=>S.kernel.penalty * fareG SU.group (M v i)) x (K.bind.penalty*b):=by rw [hU.knobs]; exact ((fare_a (hM i)).smul _).mono (Eq.le (by rw [abs_of_pos K.bind.penalty_pos]))
   exact hφ.add (minus_e (cow (hh _)) (bia (hh _) (hk _)))
 · refine Allows.mono (C:=X') ?_ ((le_max_right ..).trans ((le_max_right ..).trans hpP)); have hL : Allows n (fun v=> kL T r t' Ω (V v) (U v) (M v) i) x L:= skip_le _ fun j:Bool=>bia (he (i,j)) (minus_e ((Q₁.2 _ _ hf.le ht (i,j)).add (Q₂.2 _ _ ha hk (i,j))) (hl _))
   have hD : Allows n (fun y=>kD T r t' Ω (V y) i) x X:=by
      apply skip_le (fun j:Bool=>_) _
      intro j; let u':= (i,j); refine (((bia (he u') (minus_e (he u') (((Q₁.2 _ _ hB hb u').add (Q₂.2 _ _ hB hh u')).add (Q₃.2 _ _ hB (Q₃.1 _ _ hc.le he) u')))).smul (1/2)).mono ?_).germ ?_
      · unfold D B; rw [abs_of_pos (by norm_num)] -- tune parentheses
      apply Eventually.of_forall; intro y; change (1/2:ℝ)*_= _; ring -- tune
   have hp : Allows n (fun y=>hallP Ω T.low (V y) i t') x P₂:= (creek i _ _ hY.1 hY.2 Hx Ω p').mono (le_of_eq (by unfold P₂ murP; rw [hl']))
   exact (minus_e (skip_le _ fun j:Bool=>minus_e (bia (he (i,j)) (hl (i,j))) (cow (he (i,j)))) (hp.add (cow (he (i,true))))).add (hL.add hD)
 exact (cow (Q₃.1 _ _ hc.le he i)).mono ((le_max_right F N).trans ((le_max_left ..).trans hpP))
end YM.CF.Esti
