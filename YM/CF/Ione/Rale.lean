import YM.CF.Ione.Jost
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
local notation "f₁"=> P.B
local notation "V'Q"=> (P.supportExponent+1+1)
lemma zen_B {f:Copy n}(g: Vow.Medal P X D f h a): Vow.Medal P X D (Vow.zenS P X D f) h a:=by
 refine ⟨⟨fun i j t v=>?_ ,fun i=>?_,Measurable.ite (show MeasurableSet {v:Orbit n| Vow.visible P X D v.1} from measurable_fst ((Rue.year_s _ ping_o).measurableSet)) g.keeps measurable_const,fun i y=>?_ ⟩,?_⟩
 · unfold zenS; rw [visibly t]; congr 1; exact g.same _ _ t v
 · unfold zenS; split; exact g.lit _; exact Flour.trivial
 · unfold zenS; rw [show visible P X D _ ↔visible P X D i.1 from visiL i.1 y]; split; exact g.gaugeX ..; exact (map_zero _).symm -- tune
 obtain ⟨A,t,v,x⟩:=g.pays; refine ⟨A,t,fun i p Y y=>?_,x⟩
 refine ⟨Eventually.of_forall (fun x=> (fineShape _).allP),fun j=> Pence.germ ((v i p y).haveP j) ?_⟩
 filter_upwards [Vow.tick (Y:=Y) p] with z x; unfold SongF; dsimp only; unfold zenS; rw [if_pos (hates x)] -- tune
abbrev Mat_R(Q:Aura n→ℝ):= Γ • (∑ s:Sweep n,zeal_F s Q) -- notation hazard
lemma labourV (Q:Aura n→ℝ)(a g:ℝ)(u:∀ i:Seat n,tallB Q k a i≤g)(x:Seat n): tallB (Mat_R Q) k a x≤g:=by
 unfold Mat_R; rw [tall_s]; have he:tallB (∑ s:T0,zeal_F s Q) k a x= ∑ s:T0,tallB (zeal_F s Q) k a x:=by unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; exact sum_comm
 rw [he]; nth_rw 1 [←feed n g]; -- probably rewrite g on RHS only
 refine mul_le_mul_of_nonneg_left ?_ (envy n).le; have hx(i:Sweep n): tallB (zeal_F i Q) k a x ≤ g:=by apply le_trans _ (u ((boxA i).symm x)); exact le_of_eq (by rw [← call_Q (k:=k) i Q ((boxA i).symm x),Equiv.apply_symm_apply])
 simpa only [sum_const,card_univ,nsmul_eq_mul] using (sum_le_sum (fun i (_:i∈(univ:Finset T0))=>hx i))
lemma tally_F(A:Aura n→ℝ)(i:Aura n): Mat_R A (moldA s i)=Mat_R A i:=by
 unfold Mat_R; rw [Pi.smul_apply, Pi.smul_apply,Finset.sum_apply,Finset.sum_apply]; simp_rw [zeal_F,Function.comp_apply,hush_k]; refine congrArg _ ?_; conv_rhs=>rw [←Equiv.sum_comp (Equiv.mulLeft s)]
 rfl
lemma woof(V:Cipher n): ‖suit_Y s V‖=‖V‖:= by change ‖sings _ _ V.val‖=‖V.val‖; exact Scroll.singN _ _ _
lemma thinkT(a:ℝ): ‖(Lilt.thim n a:Cipher n)‖= ‖a‖:=by change ‖a • (1:FC (Dwell n))‖=_; rw [norm_smul,CStarRing.norm_one,mul_one]
variable {G R:Pax n}{A L C W v:Aura n→ℝ}{γ κ σ:ℝ}
-- uses EXTRA after UNKNOWN hΨ. G log cost semester untouched; R surcharge ∼3. $Universe compact tags. No Matter OEM logs on Flags.E. Support.All.$ Sharp d.
local notation "Zg"=> degreePrice P.B γ 1
variable (wisp:Wisp P F E h γ b c)(hp:1 ≤h)(hf:Sym_a F)(hr:Sym_a E)
local notation "θ"=> P.supportExponent+1+1
abbrev cashV(V:Aura n→ℝ):Pax n:=fun i v=> Lilt.thim n (V i)
structure WispE(P:BudgetPoint)(F E:Pax n)(h γ c d:ℝ):Prop where
 keep:∃ (Y:Aura n→ℝ)(R:Pax n)(L C A:Aura n→ℝ),(∀ s i,Y (moldA s i)=Y i) ∧ Sym_a R ∧ Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1)∧ (∀ i,Medal P i.val ∅ (F i) h (A i))∧ (∀ i, Medal P i.val ∅ (cashV Y i) h (L i))∧ (∀ i,Medal P i.val ∅ (R i) h (C i)) ∧ (∀ o:Seat n,tallB L P.B (P.supportExponent+1+1) o≤c)∧ (∀ o:Seat n,tallB C P.B (P.supportExponent+1+1) o≤d) ∧(∀ (i:Aura n)(v:Orbit n),visible P i.val ∅ v.1→ FeeD P F i v=cashV Y i v + E i v + R i v)∧Turf R
include wisp hp hf hr
local notation "RT"=> CashV -- remove
lemma achieve_T : WispE P F E h γ b (3*c):=by
 obtain ⟨G,R,L,C,A,Yv,t,q,w,H,Vx,Vy,Z,W⟩:=wisp.keep
 have hν:=(add_pos (add_pos P.exponent_pos zero_lt_one) zero_lt_one).le
 have ht:Sym_a (FeeD P F):=fun i x v=> spinsE i x (suit_Y i) v (fun z=>hf ..) t hp q hν 0
 choose M H' using Yv
 let T:=Mat_R M; let Y:=Mat_R L; let X:=C+(C+Mat_R C); let R':=fun i:Aura n=> zenS P i.val ∅ (R i+(G i- cashV T i)); have hz(i:Aura n)(v:Orbit n)(p:visible P i.val ∅ v.1): R' i v= FeeD P F i v - E i v - cashV T i v:=by unfold R' zenS; rw [if_pos p,Z i v p, Pi.add_apply,Pi.sub_apply]; abel
 let V:= ((1:Pane n),Classical.arbitrary (Ids n)); have he0(i:Aura n):pingS P.threshold (i.val \ ∅) V.1:=by rw [sdiff_empty]; exact ping_f P _
 have h1(A:Aura n→ℝ)(T: Aura n→ℝ)(i:Aura n)(p:‖A i‖≤T i): Medal P i.val ∅ (cashV A i) h (T i):=((Vow.Medal.oneT).rum _).big (mul_one (‖A i‖)|>.trans_le p)
 refine ⟨⟨T,R',Y,X,A,fun i j=>tally_F ..,fun i x v=>?_ ,t,q,fun i=>h1 _ _ i ?_ ,fun i=>?_ ,fun i=>labourV L _ _ Vx i,fun i=>?_ ,fun i v p=>by rw [hz i v p]; abel,fun i v B=>?_⟩⟩
 · by_cases h:visible P x.val ∅ v.1; · rw [hz x v h,hz _ _ ((yarnV (P:=P) i v x 0).mp h), ht i x v, hr i x v,map_sub,map_sub]; unfold cashV Lilt.thim; unfold T; rw [map_smul,tally_F i M x,map_one] -- T unfold
   rw [show R' x v=0 from if_neg h, show R' (moldA i x) (yellA i v)=0 from if_neg (mt (yarnV (P:=P) i v x 0).mpr h),map_zero]
 · unfold T Y Mat_R; simp only [Pi.smul_apply,Finset.sum_apply,norm_smul]; rw [Real.norm_of_nonneg (envy n).le]; apply mul_le_mul_of_nonneg_left _ (envy n).le; refine (norm_sum_le _ _).trans (sum_le_sum (fun s _=> ?_)); let U:=moldA s i
   have hx: ‖G U V‖ ≤ L U:= (w U).capF hp V (he0 _); rw [H' U,thinkT] at hx; exact hx
 · have hb(s:Sweep n): ‖M i- M (moldA s i)‖ ≤ C i+C (moldA s i):=by
      let X:= moldA s i; let V':= yellA s V; let p:= he0 i; have h':pingS P.threshold (X.val \ ∅) V'.1:=by rw [sdiff_empty] at p ⊢; exact (glowA ..).2 p
      have hD:= ht s i V; rw [Z X V' (hates h'),Z i V (hates p),H' _,H' _,hr s i V,map_add,map_add] at hD -- notation H' reduces
      have hu(u:ℝ): suit_Y s (Lilt.thim n u) = Lilt.thim n u:= by unfold Lilt.thim; rw [map_smul,map_one]
      dsimp only at hD; rw [hu] at hD; rw [←thinkT (n:=n),show Lilt.thim n (M i- M (moldA s i))= R X V'-suit_Y s (R i V) from ?_]
      · rw [add_comm]; apply (norm_sub_le ..).trans; rw [woof]; exact add_le_add ((H X).capF hp V' h') ((H i).capF hp V p)
      have hf:= sub_smul (M i) (M X) (1: Cipher n); rw [show Lilt.thim n (M i-M _)= Lilt.thim n (M i)- Lilt.thim n (M X) from hf]; -- cancel
      let A:=Lilt.thim n (M i); let B:=Lilt.thim n (M X); let C:= suit_Y s (E i V); let D:=R X V'; let G:=suit_Y s (R i V); change B+C+D=A+C+G at hD; change A-B=D-G
      calc
         A-B = A+C+G - (B+C+G):=by abel
         _ = D-G:=by rw [← hD]; abel
   have hd: G i- cashV T i=cashV (M-T) i:=by rw [H']; exact funext fun _=> (sub_smul ..).symm
   unfold R'; apply zen_B; rw [hd]; refine (H i).plus (h1 _ _ i ?_)
   let e(s:Sweep n):= M i-M (moldA s i); have hg:(M-T) i= plight_C n • (∑ i,e i):=by
      unfold T Mat_R e; rw [Pi.sub_apply, Pi.smul_apply,Finset.sum_apply, sum_sub_distrib,smul_sub,oath_r]; rfl
   rw [hg,norm_smul,Real.norm_of_nonneg (envy n).le]; refine le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun j _=> hb j))) (envy n).le) ?_; rw [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_add,feed]; simp only [Pi.add_apply,Mat_R,Pi.smul_apply,Finset.sum_apply]; exact le_rfl
 · unfold X; rw [tall_add,tall_add]; exact (add_le_add (Vy _) (add_le_add (Vy _) (labourV _ _ _ Vy i))).trans_eq (by ring)
 · unfold R' zenS; split; next p=> rw [Pi.add_apply, Pi.sub_apply,W i v B,H' i]; rfl
   next p=>rfl
end YM.CF.Ione
