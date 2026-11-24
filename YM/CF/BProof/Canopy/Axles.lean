import YM.CF.BProof.Canopy.Rotor
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro.Recast
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable {n:Side}
open Haro
variable (k:ℕ)(u:1≤k)(M: Male) -- Male open
include u
def recast : Op (Single n)→ₗ[ℝ] Op Slot:=by
 let L(F:Op (Single n))(p:ℝ):=potion k M (heroP F) (bout 0 p)
 have he(F):DifferentiableAt ℝ (L F) 0:=by
    have hp:DifferentiableAt ℝ (fun p:ℝ=> heroP F (bout 0 p)) 0:=by unfold heroP; apply DifferentiableAt.fun_sum; intro j _; unfold Laurent.mode Tap.bout; fun_prop
    let h:= (barox k u M 0).differentiableAt; exact (((differentiableAt_const 1).sub h).mul hp).mul h
 let T: Op (Single n)→ₗ[ℝ] Op Slot :=
   { toFun:=fun F=>zeus k M (heroP F)
     map_add':=fun i j=>by
       have hp:L (i+j)= L i+L j:=by
          funext x; unfold L potion; let v:=bout 0 x; rw [show heroP (i+j) (bout _ _)=heroP i v+heroP j v from ?_, mul_add,add_mul]; rfl; apply eq_add_of_sub_eq; rw [←Exa.weights,add_sub_cancel_right]
       change spaX (deriv (L _) 0) 0=spaX (deriv (L _) 0) 0+spaX (deriv (L _) 0) 0; rw [hp,deriv_add (he i) (he j),pedal]
     map_smul':=fun r F=>by
       have hp:L (r • F)= fun x:ℝ=>r • L F x:=by funext x; unfold L potion; rw [coreF,Matrix.mul_smul,Matrix.smul_mul]
       change spaX (deriv (L _) 0) 0=r • spaX (deriv (L _) 0) 0; rw [hp]; change spaX (deriv (r • L F) 0) 0=_; rw [((he F).hasDerivAt.const_smul r).deriv,pedal_r] }
 exact T
omit u
end YM.CF.Haro.Recast
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
namespace YM.CF.Sour.Digit
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral Axial
open Levier Salt Ione Nacre BondL
open scoped YM.CF.Mew YM.CF.Sour.Axial
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁ Wk:ℝ}{q:ℕ} {m:Cash P}
lemma bump {E:RegBudget n}(u:IncX Utrue E P W a)(p:a≤b):IncX Utrue E P W b:=by obtain ⟨⟨F,w,r⟩,t⟩:=u; exact ⟨⟨F,w,fun i=>(r i).trans p⟩,t⟩
lemma inc_scale {E:RegBudget n}(u:IncX Utrue E P W a)(x:ℝ)(t:0 ≤ x): IncX Utrue (x • E) P W (x * a):=by
 have he:= thin_P P E x (show Books P E W a from ⟨u.weight,fun _ k=> k.elim⟩); rw [abs_of_nonneg t] at he; exact ⟨he.weight,fun s S V v i U=> by simp only [Pi.smul_apply,map_smul]; exact congrArg _ (u.face s S V v i U)⟩
lemma inc_sub {E E':RegBudget n}(p:IncX Utrue E P W a)(u: IncX Utrue E' P W b)(h:Books P (E-E') W c):IncX Utrue (E-E') P W c:=⟨h.weight,fun s g V v i U=> (congrArg₂ (·-·) (p.face s g V v i U) (u.face s g V v i U)).trans (map_sub ..).symm⟩
namespace Trial
variable (Y:Trial T S P U q t d W z₀ z₁ a b c Wk)
local notation "F"=> Y.F
local notation "k"=> Y.k
variable {e:ℝ}{B G:Stream n}(h:B.Bears P m (cipherK q) W e)(h':G.Bears P m (cipherK q) W e)(p:Reservoir P m R W a b c e Wk)[Nonempty (ΘS R)]
local notation "A"=> orchard F R p.fp.le
local notation "φ"=> board P R W a b c
variable {hd ε:ℝ}{i j: ΘS R}
include p
lemma lyre (i:ΘS R) : IncX Utrue (tuneL k F i.val) P W (yard P R W) ∧ IncX Utrue (tuneW k F i.val) P W φ:=by
 rw [←goalL k F p.fp.le i,← goalW k F p.fp.le i]
 exact ⟨(A).starH (k).tile (k).pos W (k).hw i (k).paid (k).hv (k).y (k).hx (k).v (k).w (pureC F p.fp.le Y.pf) p.aa p.ny,(addT P ((A).pay_r (k).tile (k).pos W (k).hw i (k).paid (k).hv (k).y (k).hx (k).v (k).w p.aa p.ny p.ab) ((A).pay_z (k).tile (k).pos W (k).hw i (k).paid (k).hv (k).y (k).hx (k).v (k).w p.aa p.ny p.ab))⟩
include h
lemma nY (i:ΘS R): let N':= wave k F B.B i.val; Sym_a N' ∧ Bake.Turf N':=by
 obtain ⟨u,v⟩:= h.bark.prices (zero_le_one.trans (k).hw); let T':=kernel_p k F p.fp.le i; let c:=Cash.clock p.toWarrant v (cop F p.toLoomPay) (k).hw T'.dice; obtain ⟨s,u',w,-⟩:= Cash.logPay p.toWarrant v (k).hw T' c
 intro N'; obtain ⟨e₁,e₂⟩:= lyre Y p i; have tz: tuneZ k F i.val=tuneL k F i.val+tuneW k F i.val:=rfl; have hz:= addT P e₁ e₂; rw [←tz] at hz
 have hv0:Bake.Turf (Fine (Y.flow B i.val)):=by rw [←flow_eq Y p i]; exact (A).roof_K (k).tile (k).pos W (k).hw i B.B (k).paid (k).hv (k).y (k).hx (k).v (k).w h.mark
 refine ⟨Larch.veil_Ψ _ s (k).hw u' w (show Sym_a (Fine (Y.flow B i.val)) from ?_) h.Ω hz,Larch.π_u _ hv0 h.mark⟩; rw [←flow_eq Y p i]; exact (A).spark (k).tile (k).pos W (k).hw i B.B (k).paid (k).hv (k).y (k).hx (k).v (k).w v.fr h.mark h.prior c (Cash.Φk P) Cash.Ψk (Cash.ΦΨ P)
include h'
lemma TWin (u:Court B.B G.B P (cipherK q) m R W ε hd i j) (K:Books P (G.E-B.E) W (ε*(e/4))):IncX Utrue (Y.cash G j.val-Y.cash B i.val) P W (e*(9*ε/32+3*hd/32)):=by
 have v:= Court.glyph k F p.toLoomPay u; let N:= wave k F G.B j.val; let N':= wave k F B.B i.val; have ht:= nY Y h p i; have he:= nY Y h' p j
 obtain ⟨X,s,r⟩:= beauty.mp v.2.2
 have hx:cast_E N Y.Tp-cast_E N' Y.Tp=cast_E (N-N') Y.Tp:=by funext i U; exact (smul_sub (bassH (Bake.lagE i)) (N _ (U,Y.Tp)) (N' _ (U,Y.Tp))).symm
 have H:= worth_R P (N-N') Y.Tp (fun l D q=> by change N _ _- N' _ _= _; rw [show N _ _= _ from he.1 l D q, show N' _ _= _ from ht.1 l D q]; exact (map_sub ..).symm) (fun l V w=>congrArg₂ (·-·) (he.2 l V w) (ht.2 l V w)) (zero_le_one.trans (k).hw) (v:=X) s r
 rw [show Nor.reserveT _ _ _ _*_=(ε+hd)*m.Tr from (by unfold Cash.Tr Cash.Nr tintK; ring)] at H
 obtain ⟨l,t⟩:= tone hd u.ah (j.val-i.val) u.dist i; change IncX _ (_+cast_E N _-(_+cast_E N' _)) _ _ _; rw [add_sub_add_comm,add_sub_add_comm,hx,←map_sub (tuneW k F),t,map_smul]; refine bump (addT P (addT P (inc_sub h'.core.firm h.core.firm K) (inc_scale (lyre Y p l).2 hd u.ah)) H) ?_
 have hu:=mul_le_mul_of_nonneg_left p.post u.pos.le; nlinarith only [mul_le_mul_of_nonneg_left p.port u.ah, hu]
lemma wavy (u:Court B.B G.B P (cipherK q) m R W ε hd i j)(K:Books P (G.E-B.E) W (ε*(e/4))) : dist (Y.onZ h' p j) (Y.onZ h p i)≤ R*((9*ε+3*hd)/256):=by
 let a:= Y.cash G j.val; let b:= Y.cash B i.val
 have hp:= (axeK Y.T₀ P Y.M (a-b) Y.z (TWin Y h h' p u K) Y.l (k).hw Y.u Y.j Y.ok).2.2
 let Q(x):=zeus Y.j Y.M (Haro.heroP (StackL x Y.T₀)); have he(x l:RegBudget n): Q (x-l)=Q x-Q l:=by
    change Recast.recast Y.j Y.ok Y.M (StackL (x-l) _) = _; rw [show StackL (x-l) Y.T₀=StackL x Y.T₀-StackL l Y.T₀ from (eq_sub_iff_add_eq.mpr (by rw [← mark_T,sub_add_cancel])),map_sub]; rfl -- tune
 have hz:=expect_δ p (k).hw; rw [show zeus _ _ _= Q a-Q b from he a b] at hp; change dist (riseV (Y.onZ h' p j)) (riseV (Y.onZ h p i))≤_; rw [dist_eq_norm,on_tag,on_tag]; refine hp.trans_eq ?_; unfold tiltB at hz; linear_combination (norm:=ring_nf) hz * ((9*ε+3*hd)/32)
end Trial
end YM.CF.Sour.Digit
