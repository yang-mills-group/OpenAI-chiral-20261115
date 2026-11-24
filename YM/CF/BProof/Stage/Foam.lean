import YM.CF.Pso.Fume
import YM.CF.BProof.Stage.Watch
import YM.CF.BProof.Floral.Wisp
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
open YM.CF.Floral
open scoped YM.CF.Mew
variable (E F:ℂ→ Pax n)(L:ℝ)(Tp:Orbit n)(tV:Tp.1=1) (u:1<L)(p:1≤h)(A:∀ z∈disk L,Wisp P (F z) (E z) h a b c)(hE:∀ (i:Aura n)(y:Orbit n),Hol (disk L) (fun z=>E z i y))(hF:∀ (i:Aura n)(y:Orbit n), Hol (disk L) (fun z=>F z i y))
-- we use (1) and (0), respect endpointTicket ∀V∈Orbit
local notation "R'" z:max=> (FeeD P (F z)-E z)
local notation "w_"=> (P.supportExponent+1+1)
local notation "X_" z:max => (curr_X P (E z) (F z) Tp)
local notation "U_" z:max => (curr_r P (E z) (F z) Tp)
include tV u p A hE hF
lemma ocean_L (dV: (L-1)⁻¹≤d): HiveQ (fun i:Aura n=> ‖(U_ 1) i- (U_ 0) i‖) P (P.supportExponent+1+1) (2*d*c) ∧ Binder P h (P.supportExponent+1+1) (curr_X P (E 1) (F 1) Tp-curr_X P (E 0) (F 0) Tp) (6*d*c):=by
 let Ω:=disk L; let r(z:ℂ)(i:Aura n)(x:Orbit n):= Mew.chipV (n:=n) ∅ ((R' z) i x); let g(z:ℂ)(i:Aura n):= r z i Tp; choose G R Lx C A' T v e W f w t Vt uZ using fun z:ℂ=> fun h:z∈Ω=>(A z h).keep -- order
 have hw:0≤ w_:=by linarith [P.exponent_pos]
 let Q(g:ℂ):= g • (1:Copy n)
 let Y(z)(i:Aura n):= zenS P i.val ∅ ((R' z) i-Q (g z i))
 have hQP(i:Aura n)(z:ℂ):Medal P i.val ∅ (Q z) h ‖z‖:=(medal_scale z Medal.oneT).big (by rw [mul_one])
 have he(i:Aura n):pingS P.threshold (i.val\∅) Tp.1:=by rw [tV,sdiff_empty]; exact ping_f P _
 have hχ(i:Aura n):= hates (he i)
 choose Xκ ρ using fun z (p:z∈Ω) i=> T z p i
 have hh (z:ℂ)(p:z∈Ω)(i:Aura n)(x:Orbit n)(l:visible P i.val ∅ x.1) : (R' z) i x= ((Xκ z p i:ℂ) • (1:Cipher n)) +R z p i x:=by
    change FeeD P _ _ x - E z i x =_; rw [Vt z p i x l, ρ,add_right_comm,add_sub_cancel_right]; rfl
 have hH (z)(l:z∈Ω)(i:Aura n):‖g z i-(↑(Xκ z l i):ℂ)‖ ≤ C z l i:=by
    unfold g r; rw [hh z l i Tp (hχ i), map_add,map_smul, show Mew.chipV ∅ (1:Cipher n)=1 from ?_, smul_eq_mul,mul_one,add_sub_cancel_left]; swap; · change Pastry.crumb (1:FC (Dwell n)) ∅=1; simp [crumb]
    exact (YM.CF.norm_entry (R z l i Tp).val _ _).trans ((f z l i).capF p Tp (he i))
 have hv(z)(l:z∈Ω): Binder P h w_ (Y z) (2*c):=by
    refine beauty.mpr ⟨fun i=>2*C z l i, fun i=>?_, fun i=>?_⟩
    · let t:= Xκ z l i; have hk: Y z i=zenS P i.val ∅ (R z l i+Q ((↑t:ℂ)-g z i)):=by
         funext x; unfold Y zenS; split; next q=> rw [Pi.sub_apply,Pi.add_apply,hh z l i x q]; simp [Q,t, sub_smul]; abel -- tune
         next q=>rfl
      rw [hk]; exact zen_B P (((f z l _).plus (hQP i _)).big (by rw [norm_sub_rev]; unfold t; linarith [hH z l i])) -- tune t
    unfold tallB; simp_rw [mul_assoc, ← mul_sum]; exact mul_le_mul_of_nonneg_left (t z l i) (by norm_num)
 have hQ(i:Aura n)(x:Orbit n): Hol Ω fun z=>(R' z) i x:=by
    let X(z:ℂ):=if h:z∈Ω then A' z h else 0
    let k:=v 0 (d0 u); exact (Rive.lore_pit F P p hF X hw (fun i g=>by unfold X; rw [dif_pos g]; exact v i g) (fun i g=>by unfold X; rw [dif_pos g]; exact e i g) (ready_pos _ _ k|>.le) k.2.2.2.1 isOpen_ball i x).sub (hE i x)
 have hYG(i:Aura n): Hol Ω fun z=>g z i:= (Mew.chipV (n:=n) ∅).differentiable.comp_differentiableOn (hQ i Tp)
 have hY(i:Aura n)(x:Orbit n): Hol Ω fun z=>Y z i x:=by
    unfold Y zenS; split; swap; · exact differentiableOn_const _
    exact (hQ i x).sub ((hYG i).smul (differentiableOn_const (s:=Ω) (1:Cipher n))) -- tune implicit 𝕜
 let z₀:= (0:ℂ); have hc:0≤c:=by have hh:=(hv 0 (d0 u)).pos hw (zero_le_one.trans p); linarith -- dot.Note η: p variable overload
 -- estimate imaginary arcs
 have hF0:HiveQ (fun i=>‖g 1 i-g 0 i‖) P w_ (2*d*c):=by
    intro o; unfold tallB; simp_rw [mul_comm ‖_‖]; let q(i:Aura n):=currency P.B w_ i.val; let S:= (univ:Finset (Aura n)).filter fun i=> o∈i.val; have hs(z)(l:z∈Ω):(∑ i∈ S,q i*|(g z i).im|) ≤ c:=by
       apply le_trans _ (t z l o); apply sum_le_sum; intro i _; rw [mul_comm]; have he:= ((Complex.abs_im_le_norm (g z i-Xκ z l i)).trans (hH z l i)); simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at he; exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    exact (imaginary_t S q (fun i z=>g z i) u (fun i _=>(Real.exp_pos _).le) (fun i _=>hYG i) hs).trans (mul_le_mul_of_nonneg_right (by rw [div_eq_mul_inv]; gcongr) hc)
 have hD: HiveQ (fun i:Aura n=> ‖(U_ 1) i- (U_ 0) i‖) P w_ (2*d*c):=by
    intro j; apply le_trans _ (labourV _ _ _ hF0 j); apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    simp only [curr_r, Mat_R, Pi.smul_apply, Finset.sum_apply]; let LL(g:Aura n→ℂ):=fun i=>Complex.re (g i); let M(g:Aura n→ℝ):= (∑ s:Sweep n,g (moldA s i)); change ‖plight_C n • M (LL (g 1))-plight_C n • M (LL (g 0))‖ ≤ plight_C n • M (fun i=>‖g 1 i-g 0 i‖) -- defeq sums Pi orientation? tune
    rw [←smul_sub, norm_smul,Real.norm_of_nonneg (envy n).le]; apply mul_le_mul_of_nonneg_left _ (envy n).le; unfold M LL; rw [←sum_sub_distrib];  refine (norm_sum_le ..).trans (sum_le_sum fun j p=> ?_); exact Complex.abs_re_le_norm (g 1 (moldA j i)-g 0 (moldA j i)) -- tune
 refine ⟨hD,?_⟩
 have ht:Binder P h w_ (Y 1-Y 0) (2*d*c):= Binder.diff u p hv (fun i v h=>hY i v) hw (by
   rw [div_eq_mul_inv]
   calc
    2*c*(L-1)⁻¹ ≤ 2*c*d:= by gcongr
    _ =_:= by ring)
 let JZ: Pax n:=fun i=>zenS P i.val ∅ (Q (g 1 i-g 0 i-(((U_ 1) i-(U_ 0) i:ℝ):ℂ)))
 have hh(i):Medal P i.val ∅ (JZ i) h (‖g 1 i-g 0 i‖+‖(U_ 1) i-(U_ 0) i‖):=by
    refine zen_B P ((hQP i _).big ?_); simpa only [Complex.norm_real] using norm_sub_le (g 1 i-g 0 i) ((((U_ 1) i-(U_ 0) i:ℝ):ℂ))
 have hk:Binder P h w_ JZ (4*d*c):= by refine beauty.mpr ⟨_,hh,fun i=>(((tall_add (k:=P.B) (fun i=>‖g 1 i-g 0 i‖) _ w_ i)).le.trans (add_le_add (hF0 i) (hD i))).trans_eq ?_⟩; ring
 have ha (x y a b g h:Cipher n): x-a-(y-b)=x-g-(y-h)+(g-h-(a-b)):=by abel
 have hg:X_ 1-X_ 0= Y 1-Y 0+ JZ:=by
    funext i v; simp only [curr_X, Pi.sub_apply, JZ, Pi.add_apply, Y, zenS]; split; swap; · simp
    simp only [Q, Pi.smul_apply, Pi.one_apply,Complex.ofReal_sub,sub_smul,Complex.coe_smul]; exact ha _ _ _ _ _ _
 rw [hg]; exact Wallet.mono (ht.plus hk) (Eq.le (by ring))
end YM.CF.Ione
