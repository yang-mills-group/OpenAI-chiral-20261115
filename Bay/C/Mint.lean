import Bay.C.Flat
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes Leaf



open Levier Urn Ione
open Peaks

set_option maxRecDepth 3500
set_option synthInstance.maxHeartbeats 160000
open Py Py.Rate Thera Dial Nacre Laic
open LocalLimit Preparation

open Lor Py.Rate.BScale Push.Uniform
open Pressure SectorNext.Remainder Nor
open Push.AbsoluteSums Trees Roots
open BPress (NPL PL lscale lscale_late lscale_one)
local notation "VΔ" => Buffered.Afterglow.Tower.VacuumSelection.Spine
open Salt SU Swell QuadClock Mew Vow.TreasuryFog
open BProof.Bide

variable {w:Berth}{a b c:ℝ}{x:Site w.side}{o:Seat w.side}{m t:ℕ}{f:w.First}

open D hiding quiver
open Carol Zephyr.Chern

lemma sixP {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{g:E→ℂ}
  (h:Jet.Allows 6 g x c):Pence 6 g x (7*c):=by
 refine ⟨h.smooth,?_⟩
 apply le_trans _ (show (∑ _i∈range (6+1),c)≤7*c from by simp[sum_const])
 apply sum_le_sum; intro i t
 unfold noble;rw[one_pow]
 exact (mul_le_of_le_one_left (norm_nonneg _) (div_le_self zero_le_one (Nat.one_le_cast.mpr i.factorial_pos))).trans (h.norm_le _ (Nat.le_of_lt_succ (mem_range.mp t)))

-- mark receives mask's pings on roost B o; Herb at larger 24B.
section
variable {N:Side}{p:BudgetPoint}{o:Seat N}{D L h:ℝ}{k q:ℕ}{F:Pane N→ℂ}
def mint (F:Pane N→ℂ):Firing N:=fun x=>F x.1 • 1
abbrev freshV(p:BudgetPoint)(o:Seat N)(F:Pane N→ℂ)(L:ℝ):Prop:=
 ∀ (v:Pane N), v∈setAwning p o →∀ z:Support (More N),
    Pence p.order (fun x=>F (pressQ p z v x)) 0 L
lemma freshH
   (h0:Vinyl p o k a b F)
   (l:0≤L) (f:freshV p o F L)
   (Y:Aura N)(g:areaMark p o ⊆ Y.val):
 Herb p q Y h (mint F) L:=by
 refine ⟨l,?_,fun _ _ _ _ _=>rfl⟩
 intro X t D _ _
 have H:AuraOp p X D (mint F) h L:=by
   rw[←mul_one L]
   refine AuraOp.sat h (fun i=>F i.1) (1:FC (Dwell N)) (Ark.one _) l ?_
   intro V u Z _
   by_cases j:V.1∈setAwning p o
   · exact f V.1 j _
   have hm:roost p.B o ⊆ X.val:= (roost_expand (Nat.le_add_left ..)).trans (g.trans t)
   have i:= mt (pingFix hm u).mpr j
   refine Pence.germ ⟨(Pence.const _ (0:ℂ)).smooth,(Pence.const _ _).earned.trans ((norm_zero.le).trans l)⟩ ?_
   filter_upwards [whileLit (Z:=Z) u] with x v
   let w:Orbit N:=(pressQ p Z V.1 x,V.2)
   exact (h0.fence _ (mt (pingFix (i:=w) hm v).mp i)).symm

 refine ⟨⟨Measurable.smul (h0.meas.comp measurable_fst) measurable_const,
       fun i=>Sector.one.scale _,?_,?_⟩,H.pay⟩
 · intro i j _ _ u _
   unfold mint
   rw[h0.localV i.1 j.1 (agrees_mono u (coe_subset.mpr (g.trans t)))]
 intro i t _
 unfold mint
 rw[h0.hue, Scree.sauce,singT,win_c,win_i,twist_scalar,map_one]; rfl
end

def pollen(p:BudgetPoint){N:Side}(o:Seat N)(F:Pane N→ℂ):Bag N:=
 fun A => if A=plank 0 p.B o then mint F else 0
lemma pollenPilot (o:Seat w.side) (F:Pane w.side→ℂ):
 Grass w (fun x=>F x.1 • 1) (pollen w.p o F):=by
 intro x _ d y
 have p:(∑ A,pollen w.p o F A x)=F x.1 • 1:=by 
    rw [sum_eq_single (plank 0 w.p.B o) (fun i _ ne=>by rw [pollen, if_neg ne];rfl) (by simp)]
    rw[pollen,if_pos rfl];rfl
 rw [p,act_smul,act_smul,act_one,act_one]
 exact map_smul _ _ _


lemma mintLoan{N:Side}{p:BudgetPoint}{u:Seat N}
 {q k:ℕ}{h L:ℝ}{F:Pane N→ℂ}
 (y:Vinyl p u k a b F)
 (j:0 ≤L)(t:freshV p u F L):
 Barrage p q (grooveB 24 p u) h (pollen p u F) (rScale p) (padFee 0 * L) (padFee 0 * L):=by
 let g:=plank 0 p.B u
 have a:areaMark p u ⊆g.val:=roost_expand (by have hb:=p.B_pos;unfold plankN;omega)
 have b:grooveB 24 p u ⊆ g.val:=roost_expand (Nat.mul_le_mul_right p.B (by decide))
 let l:=Barrage.single (P:=p) (s:=rScale p) (q:=q) (h:=h) g _ (Flight.once (freshH y j t g a)) b
 have e: rScale p≤9:=by
    have b:1 ≤ (p.B:ℝ):=Nat.one_le_cast.mpr p.B_pos
    unfold rScale;linarith only [div_le_self (by norm_num:0 ≤ (8:ℝ)) b]
 have v:L*Sour.tact (rScale p) p.B g ≤ padFee 0*L:=by
    rw[mul_comm L]
    refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) j
    have w:=Corona.tile u (plankN 0) p.B p.B_pos
    exact mul_le_mul e (by unfold Sour.widthK; exact_mod_cast w) (Nat.cast_nonneg _) (by norm_num)
 exact l.bigR v v

variable {D' r T e:ℝ}
-- cost PL uses k≤p.B.
abbrev blueC (b D' T:ℝ)(s:ℝ):=
     7*((D'*b*(12*lscale s)^2+b)*2+T*b)
def quoteZ(b D' T:ℝ):ℝ→ℝ:=fun x=> padFee 0*(blueC b D' T x)
lemma quoteZP(b D' T:ℝ): PL (quoteZ b D' T):=
 (PL.const (padFee 0)).mul ((PL.const 7).mul (((((PL.const (D'*b)).mul (((PL.const 12).mul PL.scale).pow 2)).add (PL.const b)).mul (PL.const 2)).add (PL.const _)))

lemma penceV {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{f:E→ℂ}(h:Pence t f x b):‖f x‖≤b:=by
 refine le_trans ?_ h.earned
 have a := single_le_sum (f:=fun i=>noble 1 i f x) (fun i _=>pos_nob zero_le_one i)
      (mem_range.mpr (Nat.zero_lt_succ t))
 simpa only[potash,Nat.succ_eq_add_one,noble,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
  norm_iteratedFDeriv_zero,one_mul] using a

abbrev ruby (w:Berth)(x:Site w.side)(f:w.First):Pane w.side→ℂ:=
 fun v=>w.pearlZ x f v
lemma issue (A:Canal w a D' r T e)(g:w.Rig a c m)
 (h:w.Before a b m x f):
 let z:= w.Q * blueC b D' T w.x
 let _u:= (litP w.K w.p (node x) f.X)
 let H:= ruby w x f
 0≤z ∧ Vinyl w.p (node x) (w.p.B/10) w.d (‖(w.price:ℂ)‖*b) H ∧
   freshV w.p (node x) H z ∧
   Accompanies (areaMark w.p (node x)) z (w.Z130 x f) (fun v=>H v.1 • 1) :=by
 intro z u H
 let p:=w.p
 have e₁ := saleAwning (Berth.clearance g) (boxSeal h.stone g.pulse.hint.le)
 have w0:= (Vinyl.color e₁).scale (w.price:ℂ)
 have b0:= (Vinyl.color e₁).nonneg

 have z0:0 ≤ z:=by
    have i:= A.t.dp;have j:=A.p.dp;have qp:= g.qq
    unfold z blueC;positivity
 have τ:w.price*p.threshold^2=w.Q:=by
    have ht:=w.p.threshold_pos
    unfold p Berth.price
    rw[g.threshold] at ht ⊢
    exact div_mul_cancel₀ _ (pow_pos ht _).ne'
 have hy:freshV p (node x) H z:=by
    intro V j Z
    have hm: w.p.B/10+1≤ w.p.B:=by have t:=w.p.B_pos;omega
    have i := helmPay h.stone g.pulse.hint.le A.t A.p A.hw (flatZ g h A.cool)
        A.hp A.gen hm j (Berth.clearance g) (Classical.arbitrary _) (unrest Z p.B) A.ht
    have y: Jet.Allows 6 (fun v=>u (pressQ p Z V v)) 0 (blueC b D' T w.x / 7 * p.threshold^2) :=by
       refine i.mono (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
       rw [blueC,mul_div_cancel_left₀ _ (by norm_num)]
       have t:=A.t.dp
       have e:1 + (↑(w.p.B/10:ℕ):ℝ) ≤ lscale w.x:=by
          unfold lscale; rw [← g.sizeB];gcongr
          exact Nat.div_le_self ..
       unfold tide clipped; gcongr
    have h0:= (sixP y).σ w.price
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Berth.huePos g).1,
      show 7*(blueC b D' T w.x /7*p.threshold^2)=p.threshold^2*blueC b D' T w.x from by ring, ←mul_assoc,τ] at h0
    have o:p.order=6:=g.order
    rw[o]
    exact h0
 have k:Vinyl w.p (node x) (w.p.B/10) w.d (‖(w.price:ℂ)‖*b) H:=w0
 have d:=(glint_fit e₁).scalar (w.price:ℂ)
 refine ⟨z0,k,hy, ⟨d.basis,d.paid,fun V=>?_⟩,fun _=>Sector.one.scale _,?_⟩
 · rw [Berth.zPearl,norm_smul,norm_one,mul_one]
   by_cases i:V∈setAwning p (node x)
   · have b:= penceV (hy V i ∅)
     rw [pressQ,smul_zero,Forge.born] at b
     exact b
   change ‖H V‖≤_
   rw[k.fence V i,norm_zero];exact z0
 intro X;rw[Berth.zPearl]

lemma Grass.scale{Y:phy w.side}{Z:Bag w.side}(q:ℂ)(g:Grass w Y Z):
 Grass w (q • Y) (q • Z):=by
 intro x p d y
 have h:=g _ p d y
 simp only [Pi.smul_apply,←Finset.smul_sum]
 rw[act_smul,act_smul,map_smul,h]

def mineX (w:Berth)(x:Site w.side)(o:Seat w.side)(f:w.First)(b D T:ℝ)(t:ℕ):
 SealV w.side:=
 let r:=meltZ t w.x
 let u:=ruby w x f
 ⟨o,areaMark w.p (node x),r*(w.Q * blueC b D T w.x),
    ((r:ℂ) • w.Z130 x f),
    ((r:ℂ) • (fun v=>u v.1 • 1)),(r:ℂ) • pollen w.p (node x) u⟩
abbrev lamRuby (b D T:ℝ)(t:ℕ):ℝ→ℝ:=fun x=>meltZ t x * quoteZ b D T x

lemma givenZ (A:Canal w a D' r T e)(g:w.Rig a c m)
 (h:w.Before a b m x f) (k:w.Tall)(t:ℕ)
 (y:o∈grooveB 24 w.p (node x)):
 Grant w (snowF w.P.par.R (lamRuby b D' T t)) (lamRuby b D' T t)
  (mineX w x o f b D' T t):=by
 obtain ⟨z,H,v,i⟩:=issue A g h
 let u:=meltZ t w.x
 have p:‖(u:ℂ)‖=u:=by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<u from meltPos ..)]
 have d:=i.scalar u;rw[p] at d
 refine ⟨locatedGlue _ _ (areaCoal w k x) y,d,
    Grass.scale (w:=w) (q:=u) (pollenPilot _ _),?_⟩

 have b: u*(padFee 0*(w.Q * blueC b D' T w.x))=lamRuby b D' T t w.x * w.Q:=by
    unfold lamRuby u quoteZ;ring
 apply Berth.rootLodge w _ y
 have c:=(mintLoan (q:=w.q) (h:=w.H) H z v).swell u
 rw[p,b] at c
 exact c
