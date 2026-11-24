import YM.CF.Buffered.Overcoat
import YM.CF.Buffered.Applause
/-!
# Apply cross-torus calculations to the actual trajectory data before launching power.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option maxHeartbeats 590000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open Mail Mail.Grok Ballad Ballad.Markwalk Py
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{C: Conveyor K}(J:Tiling K)
variable {m q:Side}
local notation "Lq"=> K.q
variable (x k:ℕ) (b: K.Allowed m x) (a: K.Allowed K.q x)(i:m=K.q*q) (T:Flipbook K J C x)
local notation "Vδ"=> mesh J.d' K.R.L k
local notation "Fδ"=> C.warm m x
local notation "Qδ"=> C.warm K.q x
lemma screen₂ (K:Calibration) {m q:Side} (k:ℕ) (i:m=K.q*q): Planck (mesh m K.R.L k) (mesh K.q K.R.L k) q :=⟨by rw [i]; unfold mesh; push_cast; ring⟩
abbrev certV (K:Calibration){m q:Side}(k:ℕ)(i:m=K.q*q): Planck (cell m K.B K.R.L k) (cell K.q K.B K.R.L k) q:= SugarGrid (screen₂ K k i) K.B
abbrev adjunct (K:Calibration)(m:Side)(k:ℕ): (cell m K.B K.R.L (k+1)).val=(cell m K.B K.R.L k).val*K.R.L.val:= (Vale.apt m K.B K.R.L k).exact_size
abbrev sageF(J:Tiling K) {m:Side}(k:ℕ)(p:K.takes m) := glass J k (r:=0) p
include b a
lemma costs_F : Clear (S:=K.R) (certV K k i) (certV K (k+1) i) (orderV K J k b.1) K.ℓ K.w K.D (adjunct K m k):=by
 have hp:= rim K; have he:= gauged K
 refine ⟨(by unfold nearZero at hp; omega), ?_,?_⟩
 · let A:= (certV K (k+1) i); have ht:= solid_swell J k 0 b.1; refine Subset.trans (Subset.trans ?_ ht) (fun _ p=> nested (gauge_plan A) (orderV K J (k+1) a.1) (orderV K J (k+1) b.1) he p); apply Corona.halo_mono _ (Subset.refl _); change clothRadius K.R.L K.D ≤ K.R.L.val*gross _ _ _; unfold clothRadius gross beforePad; nlinarith
 intro x v; exact nested (gauge_plan (certV K k i)) (orderV K J k a.1) (orderV K J k b.1) (show 0< (1:ℕ) by decide) (solid_pad (orderV K J k b.1) 0 (e:=K.w+1) (show 1+K.w≤ K.w+1 by omega) (Corona.halo_mono le_rfl (solid_pad (orderV K J k b.1) 0 (show (K.w+1)+nearZero K.D ≤ K.ℓ by omega)) v)) 
omit b a
private lemma same_step {p:Patch}{Q:KernelChoices}{c f: Side}{h:f.val=c.val*p.L.val}(S:StepData c f)(v:S.patch=p)(t:S.kernel=Q) : S= stepped Q h:=by cases S; congr
lemma used (K:Calibration)(m:Side)(x k:ℕ) : steps K.V m K.B x k = stepped (P:=K.R) K.K.bind (Mail.ga (adjunct K m k)):=same_step _ (K.V.L.patch_x _ (ga (adjunct K m k))) rfl
-- show Male-insensitive. form has no m argument in definition, use rfl on whole path
private theorem overpriced {P F: Side}(G:Ratio P F)(T:StepData (More P) (More F)) (j:ℕ)(ho:Odd G.count.val) (M W:Male) (Q:Op SU.Slot)(q:Chi) (d β:ℝ)(y:Loom P)(a:Mark P) : pushMark G T j Q M ho q d β y a= pushMark G T j Q W ho q d β y a:=rfl
structure LacePoint (K:Calibration)(C: Conveyor K)(J:Tiling K):Prop where
 data (m q:Side)(j:ℕ)(p:K.takes m)(i:m=K.q*q): Grok.LoomLaw2 (certV K j i) (C.loom m j) (C.loom K.q j) (halo (nearZero K.D) (glass J j (r:=0) p))
variable (Y:LacePoint K C J) {M:Melody K.B K.vertex}{B:Bool} {ℓ:ℕ}
include a b Y T
lemma coherent_step (p:k<x)(U:Mark (cell K.q K.B K.R.L k))(D:Mark (cell m K.B K.R.L k)) (h:AtSupport false (sageF J k a.1) U)(C':AtSupport false (sageF J k b.1) D)(u:CoherentV (certV K k i) U D): CoherentV (certV K (k+1) i) (liner C K.q x k U) (liner C m x k D):=by
 unfold liner nextMark; rw [used K K.q, used K m]; rw [←T.tilt_equal b a (k+1) p]; let Z:= C.warm m x (k+1); let J':=Z.J.M
 rw [overpriced _ _ K.K.j _ _ J' _ _ _ _ _ U]; obtain ⟨w⟩:=(Shots.warm_grant (T.frame m b).pair).grant k p; obtain ⟨u₁,b₁,d₁,l,H'⟩:=w.cap; obtain ⟨v⟩:=(Shots.warm_grant (T.frame K.q a).pair).grant k p; obtain ⟨u₂,b₂,d₂,l',t⟩:=v.cap
 refine Grok.rates (certV K k i) _ _ l'.bill l.bill (certV K (k+1) i) (orderV K J k b.1) (orderV K J k a.1) (ℓ:=adjunct K m k) (d:=adjunct K K.q k) ?_ K.K.j K.η K.J.d _ J' K.legal (costs_F J x k b a i) C' h u (Y.data m q k b.1 i) w.legal.1 w.legal.2 K.K.bind K.V.L.cloth Z.beta (C.lawn m b.1 k)
 change 2 ≤ (cell Lq K.B K.R.L k).val * 2; have he: 0<(cell Lq K.B K.R.L k).val:=PNat.pos _; omega
lemma dressedV {f:Mark (K.c K.q)}{g:Mark (K.c m)}(p:AtSupport false (sageF J 0 a.1) f)(t:AtSupport false (sageF J 0 b.1) g)(v:CoherentV (certV K 0 i) f g)(u:k≤x) : CoherentV (certV K k i) (postV C K.q x k f) (postV C m x k g):=by
 induction k with
 | zero=>exact v
 | succ k ih=> rw [postV_step,postV_step]; exact coherent_step J x k b a i T Y u _ _ ((T.frame _ a).onGlass J (by omega) p) ((T.frame _ b).onGlass J (by omega) t) (ih (by omega))
omit a b Y T
section basis
variable {A Z L D α L₂: Side}{R:ℕ} (V:Planck A Z D)
lemma cover_v (v:Cover)(p:∀ i, 0≤ v i∧v i<Z.val) (i:SpinIdx)(c:SU.Slot): basisC A v i c= coat (modeO V 0) (basisC Z v i c):=by
 have he: natural (wrap Z v)=v:= Mail.oh V p; have hv: pointO V 0 (wrap Z v)=wrap A v:=by rw [dime,he]
 have hz:= lime V (wrap Z v); rw [he,hv] at hz
 rw [basisC,basisC,show Lifted.winding A v=1 from hz ▸ Wings.toll_one _,show Lifted.winding Z v=1 from he ▸ Wings.toll_one _,one_smul,one_smul,basis_shell]; unfold Lifted.index; exact congrArg basisKet (show ((_,_),_)=((_,_),_) from congrArg (fun i=>((i,_),_)) hv.symm)
lemma char_coil (A':Lead R)(U:Pane Z)(i j:SU.Slot): Lead.coil A' (weave (gauge_plan V) (show Config SU.group _ from U)) i j=A'.coil U i j:=by
 have hp: onC A (weave (gauge_plan V) U)=onC Z U:=funext fun x=>by rw [onC_spec,onC_spec]; exact congrArg (fun i=> U (i,x.2)) (show (slump (gauge_plan V)).cut _=_ from Macrame.branch ..)
 unfold Lead.coil Lead.laps; rw [hp]
lemma fits_here (K:Planck (More Z) L α)(b:ℕ)(v:Cover)(p:0<b)(w: Damp L b (nodeC v-0)):∀ i,0≤ v i ∧ v i< Z.val:=by
 intro i; have he:= Mail.width K; specialize w i; rw [sub_zero] at w; rw [natM] at he; unfold nodeC at w; simp only [two_smul, Pi.add_apply,Pi.one_apply] at w; omega
lemma offered {b:ℕ}(K:Planck (More Z) L α)(g:0<b)(A':Lead R)(t:A'.Budgeted L b 0): CoherentV V (A'.chant) (A'.chant) :=by
 intro W; unfold Lead.chant Lead.birthOp; rw [map_smul,map_sum]; apply congrArg; apply sum_congr rfl; intro i _; rw [map_sum]; apply sum_congr rfl; intro j _; change (Lead.coil A' (weave _ (show Config SU.group _ from W.1)) i j) • _= _; unfold Lead.lower Lead.upper; rw [char_coil V,map_smul,map_mul, cover_v V _ (fits_here K _ A'.birth (by omega) t.born),cover_v V _ (fits_here K _ A'.death (by omega) t.gone),into_create,into_remove]
lemma chosen {b:ℕ}(K:Planck (More Z) L α)(p:0<b)(T: Melody L₂ R)(t:T.Budget L b 0)(f:Bool):CoherentV V (T.goal f) (T.goal f):=by
 have ht:=offered V K p T.first t.1; have hu:=offered V K p T.last t.2; intro W; unfold Melody.goal; cases f <;> simp only [ite_true,Bool.false_eq_true,ite_false,Pi.smul_apply, Pi.one_apply, Pi.sub_apply, Pi.mul_apply]; all_goals simp only [ht W, hu W,map_mul,map_one,map_smul,map_sub] -- tune
end basis
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.dressedV
#print axioms YM.CF.Buffered.Concert.chosen
