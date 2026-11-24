import SatinThinCrystal
import ZecaRibbon
import ZecaBill
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
set_option linter.unusedSectionVars false
set_option linter.style.whitespace false
set_option maxHeartbeats 800000

open Cardigan
/-! # A. Mosaic procedure testimonial
Obtain the end-train test by receipts on exact marks. Support geometry
for checker on origins at a possibly coarser side, with doubled
gauge grid. Projection licenses at each path index, can include
moorage over terms of positive prices or pay directly using
antibody prices of the aggregates. -/
variable {Λ:Preparation}{l:ℕ}
 (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "M" s:max i:max => Journey.side Y i s
abbrev spanSites(B:Side)(w:ℕ) := 16 * B.val * w
lemma spanShift (B:Side)(w:ℕ):ruler B*w=(spanSites B w:ℕ):=by unfold ruler spanSites; push_cast; rfl
/-- A local bill at one period. Width in ticks w on underlying N; observing
buys at W times 16 B. Origin is the checker origin, e.g. a clover
root (D interior), can travel fuel-wise under axial reflection.
Size charge paid by *lists*; not a commutative sup. M the observing
side, V its actual heated RP reading (including denominator). -/
def SparseAt (s i k:ℕ) (g:Ferry Y s i k)
 (j:Axis) (W:ℕ) (f:Family (tent Y H))(θ:ℝ):Prop:=
 ∃ (N:Side)(R w D T:ℕ)
   (α:Type)(ρ:α→Seat N)(χ:Axis→ℤ→α→α)(p:α→Mark (M s i))(seed:α),

     0<w ∧ 0<R ∧ W=R*w ∧ (M s i).val=R*N.val ∧
     Grace Λ.block ρ χ D T p (solder Y i k g.depth s)
       (fun t=> (R:ℤ)*t) (K).ℓ ∧
     Again.plusAgain Λ.block D ≤ 2 * spanSites Λ.block w ∧
     distribute Y H s i f=p seed ∧
     InBend j 0 (ruler Λ.block*w) D (ρ seed) ∧
     ∀ a:List α,outdoor ρ T a →
       (More N).val^4 ≤ a.length*(8*spanSites Λ.block w)^4 →
       ‖compass Y i k s (a.map p).prod‖ ≤ θ^a.length

private lemma hailShot {i v j:ℕ}{U ε:ℝ}(q:0<ε)(p:0≤ U)(u:U*(16/ε)≤(Journey.side Y i v).val)(t:j≤ (More (Journey.side Y i v)).val^4) : iceRate Y v i*U^j≤ ε^j:=by
 let a:=U/ε; have hp:U ≤ Real.exp a*ε:=(div_le_iff₀ q).mp ((le_add_of_nonneg_right (zero_le_one' ℝ)).trans (Real.add_one_le_exp _)); apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p hp _) (Real.exp_pos _|>.le))
 let n:= Journey.side Y i v; let Me: ℝ:= n.val; rw [mul_pow,←Real.exp_nat_mul,←mul_assoc]; rw [←Real.exp_add]; have hx: (j:ℝ) ≤ Me^4*16:=by apply le_trans (Nat.cast_le.mpr t); change ((((n.val*2)^4:ℕ):ℝ))≤_; unfold Me; push_cast; linarith
 have hz: a*16 ≤ Me:=by
    apply le_trans ?_ u; exact le_of_eq (by unfold a; ring)
 have hv:a≥ 0:=div_nonneg p q.le; have h': -(Me^5)+ j*a ≤0:=by nlinarith only [mul_le_mul_of_nonneg_right hx hv,mul_le_mul_of_nonneg_right hz (by positivity:0 ≤ Me^4)]
 exact mul_le_of_le_one_left (pow_nonneg q.le _) (Real.exp_le_one_iff.mpr h')

lemma paid_test {s i k W:ℕ}{j:Axis} (g:Ferry Y s i k)
 {f:Family K} {θ C:ℝ}(t:TestFamily K true f)
 (c:0<θ)(x:pay f C)(h:SparseAt Y H s i k g j W f θ)
 (m:IcePlot Y s i k)
 (v:C*(16/θ) ≤ (M s i).val)
 (n:ℕ)(a:ℤ)(p:2*(ruler Λ.block*W*n) ≤ ((M s i).val:ℤ))
 (q:((M s i).val:ℤ) ≤ 4*(ruler Λ.block*W*n)):
 ‖hot Y H s i k (banner j W (W*a) n f)‖≤2*θ^(4*n):=by
 obtain ⟨N,R,w,D,T,α,ρ,χ,V,seed,hw,hR,rfl,hN,b,gt,bk,lm,almost⟩:=h
 have hr:0<(R:ℤ):=by exact_mod_cast hR
 rw [hN,Nat.cast_mul,Nat.cast_mul] at p q
 have hp: 2*(ruler (tent Y H).B*w*n)≤(N.val:ℤ):=
    (mul_le_mul_iff_right₀ hr).mp (by change _*(_*(ruler Λ.block*_ * _))≤_; linarith only [p])
 have hq: (N.val:ℤ)≤4*(ruler (tent Y H).B*w*n):=
    (mul_le_mul_iff_right₀ hr).mp (by change _≤_*(_*(ruler Λ.block*_ * _)); linarith only [q])

 let r:= solder Y i k g.depth s
 let γ:=terrain Y H (Y.ir i) s
 have hl : Ribbon γ j V ρ D T (ρ seed) 0 (ruler Λ.block*w) f 1:=
    Ribbon.single t bk lm
 -- K may be underspecified in Grace application
 obtain ⟨y,L,W,hL,ly,cut,hL',bound,b0⟩:=
   full_bloom («K»:=tent Y H) b w f hl (by exact_mod_cast hw)
      (spanSites Λ.block w) (spanShift _ _) gt n hp hq a x
 let V' := (y.map V).prod; let hZ:=compass Y i k s V'
 have hh : ‖hZ‖ ≤ θ^y.length:=almost y W b0
 have he : ‖r V'-hZ‖≤θ^y.length:=by
    rw [norm_sub_rev]
    have h₀:y.length ≤ (More (M s i)).val^4:=
      bound.trans (pow_le_pow_left' (Nat.mul_le_mul_right _
          ((Nat.le_mul_of_pos_left N.val hR).trans_eq hN.symm)) _)
    exact (m g.depth V' _ (Cardigan.total b y).env ly).trans (hailShot Y c (pay_nonneg x) v h₀)
 let BB:=banner j ((R:ℤ)*w) (((R:ℤ)*w)*a) n f
 rw [Nat.cast_mul]
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (n:=L) hL'.ne').mp
 unfold hot; rw [dif_pos g.depth]
 apply cut.trans
 refine ((norm_le_norm_sub_add _ _).trans (add_le_add he hh)).trans ?_
 rw [hL, mul_pow 2, Nat.mul_comm L, pow_mul, ←two_mul]
 exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hL')) (by positivity)

variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
variable (w:ℕ)(f:Entry Y H s j strict w)(hw:0 < w)
variable {σ:ℕ→ℕ}
local notation "π" r:max=>i (a (σ r))
local notation "ζ" r:max=> k (b (σ r))

/-- See the construction notes. Warranties:
NightCop on the original path; S static at purchase (any shape);
BQueue assembled on reindexed path; only seed need match on torus;
prices of products of sparse extensive lists, with *aligned*
RP manufacture and support.
-/
theorem mosaic_norm (h:StrictMono σ)(O:IcePath Y (i∘a) (k∘b))
 {S:Finset Cover}(hS:Between K j 0 (ruler Λ.block*w) S)
 {F:ℕ→Family K}
 (hF:BQueue S F f.val.val)
 {θ:ℝ}(t:0<θ)
 (sale:∀ᶠ e:ℕ in atTop,∀ g:Ferry Y s (π e) (ζ e),
    SparseAt Y H s (π e) (ζ e) g j w (F e) θ):
 ‖boxOp Y H V s Q Qt j strict C w f hw‖ ≤ 2*θ:=by

 apply booked_operator Y H V s Q j strict C w f Qt hw h t hS hF
 obtain ⟨B,x,v,z⟩:=hF.bdd
 have he: Tendsto (fun e:ℕ=>((M s (π e)).val:ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp ((site_law Y H V Q s).comp h.tendsto_atTop)
 filter_upwards [he.eventually_ge_atTop (B*(16/θ)), z,
    h.tendsto_atTop.eventually (O s), h.tendsto_atTop.eventually (Q.finance s),sale]
    with e g c a p h n j' _ k m
 exact paid_test Y H p (aux_test (hF.whereTo e)) t c (h p) a g n j' k m
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.mosaic_norm
