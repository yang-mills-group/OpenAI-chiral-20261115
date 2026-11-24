import YM.CF.Chaff.Hub
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
open Prism
local notation "β"=> P.threshold
local notation "ζ"=> P.B
local notation "Π"=> P.power
def ailed(q:ℕ):ℝ:= 16*(2* (2*q:ℕ)+1:ℝ)^5 * Fintype.card PlaqAxes
lemma ailP(b:ℕ):0 ≤ ailed b:=by unfold ailed; positivity
lemma galeP (u:Pane N) (f: Seat N→ SU.E)(x:tangD N): Lattice.gauge f (RG.increment u x)=RG.increment (Lattice.gauge f u) (fun j=>SU.group.adjoint (f j.1) (x j)):=by funext i; simp only [RG.increment,Next.SectorChange.exp_adjoint,Lattice.gauge]; group
lemma hailF {s:ℝ}(hB:0 ≤ s)(U:Pane Λ)(p:Grove (terr _) S) (v:o∈ S)(g:pingS s (sailX P S) U)(t: 4*P.B<(Domain m B).val)(u:S.card≤ P.B):∃ z:Court m B,∀ i:reach Λ,i.1∈ S→SU.group.chord (Lattice.gauge z U i)≤ailed P.B*s:=by
 let b:= P.B; let F (z:Site ξ)(p:PlaqAxes):= Pressure.toll U (z,p)
 have ht(y':Site ξ)(g':separation o y'≤ 2*P.B)(V:PlaqAxes):F y' V ≤ s:= (LT.lt.le (g (y',V) (fun u=> Finset.disjoint_left.mp u (halo_spec.mpr ⟨o,v,g'⟩) (Work.E01.base_touched (y',V))))) -- tune
 obtain ⟨z,V⟩:= Work.E08.axial_patch o U b (2*b) (by have hp:0<b:=P.B_pos; omega) (by change 2*(2*b)< (Domain m B).val; unfold b; omega) s hB ht
 refine ⟨z,fun i q=> ?_⟩; exact V i (((p.lim _ v i.1 q).le).trans u) -- tune
-- Chart norm ray mix
abbrev dex (a c:ℝ):Prop:= ∀ u : SU.group.El, SU.group.chord u ≤ c → SU.group.lieExp (SU.group.plog (SU.group.mat u))=u∧‖SU.group.plog (SU.group.mat u)‖ ≤ a * SU.group.chord u
abbrev Brink(n:ℕ)(g D:ℝ):Prop:=∀{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (p:E→SU.group.Color)(x:E)(s),0<s→s ≤g→Allows n p x s→∀ a:SU.group.Color, ‖a‖≤ s→ Allows n (fun y=> Char.mount (p y,a)) x (D*s) ∧ ∀ᶠ y in 𝓝 x, SU.group.lieExp (Char.mount (p y,a))=SU.group.lieExp (p y)*SU.group.lieExp a
lemma braved (v:1≤ n):∃ b d:ℝ,0<b∧0<d∧ Brink n b d:=Char.pass_n SU.group n v
abbrev black_t(P:BudgetPoint):= ailed P.B * P.threshold
def leanP(P:BudgetPoint)(x:ℝ):= x*black_t P+riseH P P.B
lemma lean_P(P:BudgetPoint){b:ℝ}(q:0≤b):0<leanP P b:= by refine add_pos_of_nonneg_of_pos (mul_nonneg q (mul_nonneg (ailP _) P.threshold_pos.le)) (mul_pos P.threshold_pos (by positivity))
variable {r C0 t' tH z:ℝ} (pn:0≤C0)(u:dex C0 t')(g: black_t P ≤ t')(q:P.order=n)(u':Brink n tH r)(p':0<r)(hu: leanP P C0 ≤ tH)
local notation "α"=> leanP P C0
local notation "κ"=> r* α
local notation "Δ"=> pulseQ p R D P S
include pn u g q u' p' hu y t
lemma pool_s (X: Pane Λ)(ht:pingS β (sailX P S) X)(hl: S.card≤P.B)(hw:4*P.B < (Domain m B).val):∃ (L:Γ→Γ)(Y:Court m B), Allows n L 0 κ ∧∀ᶠ i:Γ in 𝓝 0, Agrees S (RG.increment 1 (L i)) (Lattice.gauge Y (RG.increment X (Prism.trunk P o i))):=by
 have hf:=P.threshold_pos; have hx:= lean_P P pn; obtain ⟨z,f⟩:=hailF (S:=S) (P:=P) o hf.le X t y ht hw hl
 let V:=Lattice.gauge z X; let U(j:reach Λ):= SU.group.plog (SU.group.mat (V j)); let Q(j:reach Λ):Γ→L[ℝ] SU.group.Color:= (SU.group.adjoint (z j.1)).toContinuousLinearMap.comp (efflux P S o j); have he(i:reach Λ):Allows n (Q i) 0 α:=by
    have ho: ‖Q i‖ ≤ riseH P S.card:=by unfold Q; apply (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul ?_ (life_s o y t P i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)); apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; exact (SU.group.norm_adjoint ..).le -- tune
    have hv : riseH P S.card≤ riseH P P.B:=by unfold riseH; gcongr
    exact allows_linear (ho.trans (hv.trans (le_add_of_nonneg_left (mul_nonneg pn (mul_nonneg (ailP _) hf.le))))) (by rw [map_zero,norm_zero]; exact hx.le)
 let L(x:Γ):Γ:=fun i=>if i.1∈ S then Char.mount (Q i x,U i) else 0
 have hv(i:reach Λ)(p:i.1∈ S):Allows n (fun y=>L y i) 0 κ ∧ ∀ᶠ x in 𝓝 0, SU.group.lieExp (L x i)= SU.group.lieExp (Q i x)* V i:=by
    have w:= f i p; obtain ⟨x,hk⟩:=u (V i) (w.trans g); simp_rw [L,if_pos p]; rw [← show SU.group.lieExp (U i)=V i from x]; exact u' (Q i) 0 _ hx hu (he i) _ (hk.trans ((mul_le_mul_of_nonneg_left w pn).trans (le_add_of_nonneg_right (mul_nonneg hf.le (by positivity)))))
 refine ⟨L,z,allows_pi (mul_nonneg p'.le hx.le) (fun i=> ?_),?_⟩
 · by_cases h:i.1∈S; exact (hv i h).1; unfold L; simp only [if_neg h]; exact allows_const _ (by rw [norm_zero]; positivity)
 have h(i:reach Λ):∀ᶠ x in 𝓝 0, i.1∈S → SU.group.lieExp (L x i)=SU.group.lieExp (SU.group.adjoint (z i.1) (Prism.trunk P o x i))* V i:=by
    by_cases l:i.1∈ S; swap; · exact Eventually.of_forall fun x v=> (l v).elim
    have hb(x): Q i x= SU.group.adjoint (z i.1) (Prism.trunk P o x i):=by unfold Q; rw [efflux,if_pos l]; rfl
    filter_upwards [(hv i l).2] with x g; rw [g,hb]
    intro; rfl
 filter_upwards [eventually_all.mpr h] with x v; rw [galeP]; intro j hj hk; unfold RG.increment; rw [Pi.one_apply,mul_one]; exact v j hj
variable (k:VStar n K)(f:0<H){b:ℝ}(b0:0<b)(lq:b≤1)(w:∀ i:tangD (CSide m B),‖i‖< b→Guard (RG.increment 1 i) e)(g':r*leanP P C0 ≤ b/2)
include h p A pH v l k f b0 lq w g'
lemma scent_C (X:Pane Λ)(hx:pingS β (sailX P S) X)(hl:S.card≤P.B)(hw:4* P.B < (Domain m B).val):
 Signs P o (fun x=> Pastry.pane (Δ (RG.increment X x))) (composeCost n (2*(C+C)*κ^2) 1):=by
 obtain ⟨L,y0,he,V⟩:= pool_s o y t pn u g q u' p' hu X hx hl hw
 let U(x):= RG.increment X (Prism.trunk P o x); have hs:0<κ:=mul_pos p' (lean_P P pn); have hg:κ<b:=g'.trans_lt (half_lt_self b0); let M(x):= κ⁻¹ • L x; have hp:=he.smul κ⁻¹; rw [abs_of_pos (inv_pos.mpr hs),inv_mul_cancel₀ hs.ne'] at hp
 have hm:‖M 0‖ ≤1:=hp.value; have he': ‖L 0‖ < b:=he.value.trans_lt hg; have hn:= P.order_ge; rw [q] at hn
 have ht:= Newt.portrait (f:= bedH p D) (by omega: n ≥ 2) (fruitL h k b0 lq w p (by omega) hs.le f) hs.le g' (hg.le.trans lq) hm
 apply Prism.skills; rw [q]; refine (ht.comp (f:=M) hp).germ ?_
 filter_upwards [wind_p X (Prism.trunk P o) hx, he.smooth.continuousAt.norm.eventually (gt_mem_nhds he'), V] with i vx ht k' -- tune X binder
 have hi: ‖L i‖< b:=ht; let T:=RG.increment (1:Pane Λ) (L i); let X' := Lattice.gauge y0 (U i); let z:Briar m B e:=⟨T,w _ hi⟩; have hw : Agrees S X' z.val:=fun j g z=> (k' j g z).symm
 have hy:= base_P p h A pH v l X' ((pingB (U i) y0).2 vx) hw -- v0 missing
 let C' := (D z); let K':= D (floorP m B p); have hs:(bedH p D (κ • M i))= Pastry.pane C'-Pastry.pane K':=by unfold M; rw [smul_inv_smul₀ hs.ne']; unfold bedH; rw [claw p _ (w _ hi)]
 change bedH p D _= Pastry.pane (Δ (U i)); have he: Pastry.pane (Δ (U i))=Pastry.pane (Δ X'):=by unfold X'; rw [φs_g p h A pH v l]; exact (Pastry.center_b ..).symm
 rw [hs,he,hy]; exact (congrArg (fun c:ℂ=>Pastry.pane C'-c) (Pastry.hullB (n:=Dwell Λ) _)).symm
end YM.CF.Chaff
