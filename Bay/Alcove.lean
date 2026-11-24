import Bay.Lantern
import Bay.Spout
import Zephyr.Bed
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern Zephyr

local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine
variable {N:Side}
lemma litAngle (o:Seat N)(p:BudgetPoint)(A:StemA N):
    ∀ᶠ t in 𝓝 0, Zephyr.Chern.petals A t ∈ setAwning p o:= by
 apply ((cont_petal A).tendsto 0).eventually
 rw [petal_idle]
 apply ping_o.mem_nhds
 intro i _
 rw [WilsonStartup.face_one]
 rw [SU.group.chord_one]
 exact p.threshold_pos

lemma millGlass (U:Op (Single N))(o:Site N) :
 Matrix.trace (U*millQ o)=∑ i:IS, U ((o,i.1),i.2) ((o,i.1),i.2):=by
 rw [Matrix.trace, millSt, Tye.stock]
 simp only [Matrix.diag_apply,Matrix.mul_diagonal]
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
 simp [place_x, unaryN.eq_iff] -- test

def playW (L:List Axis)(m:ℕ)(o:Site N)(M:SOp N):SOp N:=
  fun V => (M V-tickA N)*squareSum millQ m L o

def regW (P:VΩ)(s i k:ℕ):SOp (age P.run i s):=
  funde P.par.K.j (blood P.run i k s) _

local notation "fluxV" => Zephyr.Chern.stream
abbrev caul (P:VΩ)(s i k:ℕ)(m:ℕ)(l:List Axis)(x:Cover):ℝ→ℂ:=
 spout (playW l m (wrap _ x) (regW P s i k)) (fluxV _)

lemma caul_zero (P:VΩ)(s i k m:ℕ)(x:Cover):
 caul P s i k m [] x=sparSite (N:=age P.run i s) P.par.K.j (blood P.run i k s) x+
   Function.const _ (-Matrix.trace (tickA (age P.run i s)*millQ (wrap _ x))):=by
 funext r
 rw [Pi.add_apply,const_apply,caul,spout,playW,squareSum,sub_mul,Matrix.trace_sub,
 millGlass,sub_eq_add_neg]
 rfl

def nearCover (x:Cover)(i:Axis)(m j:ℕ):Cover:= x - m • step i+(j+1) • step i
lemma wrapNear (N:Side)(x:Cover)(i:Axis)(m j:ℕ):
 moveSite (wrap N x - m • step i) i (j+1)= wrap N (nearCover x i m j):=by
 simp only [map_add,map_sub,nearCover,moveSite,map_nsmul,wrap_step]

lemma caul_prepend (P:VΩ)(s i k m:ℕ)(x:Cover)(j:Axis)(l:List Axis) :
 caul P s i k m (j::l) x =
 fun r=> ∑ w∈range (2*m), caul P s i k m l (nearCover x j m w) r:= by
 funext r
 simp only [caul,spout,playW,squareSum,stripSum,Finset.mul_sum,Matrix.trace_sum,wrapNear]

def gem (f:ℝ→ℂ)(z:ℝ):Prop:= Bud f ∧ z < (bud f 2).re
lemma gemSum (u:Finset ℕ)(v:u.Nonempty)
 (f:ℕ→ℝ→ℂ)(g:ℕ→ℝ)(h:∀i∈u,gem (f i) (g i)):
 gem (fun r=>∑i∈u, f i r) (∑i∈u,g i):=by
 have a:=Bloom.sum u (fun i p=>(h i p).1.bloom)
 refine ⟨a.1,?_⟩
 rw [a.bud_eq,Finset.sum_apply,Complex.re_sum]
 exact sum_lt_sum_of_nonempty v (fun i p=>(h i p).2)

lemma goldCup (P:VΩ)(m:ℕ)(t:0 < m)(l:List Axis)(x:Cover) :
 ∃ z:ℝ,0<z ∧ ∀ᶠ s:ℕ in atTop,∀ i k, gem (caul P s i k m l x) z := by
 induction l generalizing x with
 | nil=> 
   obtain ⟨δ,h,p⟩:=(SprigFee.paid P).actual x
   refine ⟨δ,h,?_⟩
   filter_upwards [p] with s mu i k
   rw [caul_zero];exact mu i k _
 | cons a l ih=>
   choose z h p using (fun w=>ih (nearCover x a m w))
   let u:=range (2*m)

   have v:u.Nonempty := ⟨0,mem_range.mpr (by omega)⟩
   refine ⟨∑i∈u,z i,sum_pos (fun i _=>h i) v,?_⟩
   have hp:= (eventually_all_finset u).mpr (fun w _=> p w)
   filter_upwards [hp] with s T i k
   rw [caul_prepend]
   exact gemSum u v _ _ (fun w t=>T w t i k)

variable {K:Scree.Loom N}{p:BudgetPoint}{o:Seat N}{k:ℕ}{a d g c δ W B η:ℝ}{A:StemA N}{X Y M:SOp N}
/-- Bare single-root Z (multiply by Q/τ² before use as in the guide).
Actual first Pane domain. -/
abbrev pearl (K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N)(V:Pane N):ℂ:=Matrix.trace (bayonet K p o X V)
abbrev dach (K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N)(A:StemA N)(t:ℝ):ℂ:=
 pearl K p o X (Zephyr.Chern.petals A t)

/-- Includes all three coefficients compared to full expression and their cost. -/
structure Beau (f fq :ℝ→ℂ)(δ v:ℝ):Prop where
 pays:gem f δ
 full:gem fq δ
 apron(q:Fin 3):‖bud fq q - bud f q‖ ≤ v

theorem pearlJet (hm:Clearance p K k d)
   (h:BoxPay X o k c d)(t:Soak o Y a g d)
   (y:∀ V:Openc (More N) d,M V.val=X V.val+Y V.val)
   (w:Oily a d B W)(b:Temper o A B)
   (f:gem (spout M A) (δ+η))(hp:W*g≤η) :
 Beau (dach K p o X A) (spout M A) δ (W*g):=by
 obtain ⟨u,q⟩:=rootSpout w b t
 have z:= f.1.bloom.add (u.bloom.scale (-1))
 have e: dach K p o X A =ᶠ[𝓝 0] fun v=>spout M A v + -1 *spout Y A v :=by
   filter_upwards [litAngle o p A,petals_safe A hm.dept,petals_open hm.dept A] with r v g j
   dsimp [dach,pearl,spout]
   rw [box_pass hm h v (fun _ _ _=>rfl) g, y ⟨_,j⟩, Matrix.trace_add]
   ring
 have a:=z.congr e
 have l:=f.2
 have t:0≤η:=le_trans (norm_nonneg _) ((q 2).trans hp)
 refine ⟨⟨a.1,?_⟩,⟨f.1, by linarith⟩,fun i=>?_⟩
 · rw [a.bud_eq, neg_smul,one_smul,Pi.add_apply,Pi.neg_apply,Complex.add_re,Complex.neg_re]
   linarith [(Complex.re_le_norm ..).trans ((q 2).trans hp)]
 rw [a.bud_eq, neg_smul,one_smul,Pi.add_apply,Pi.neg_apply,←sub_eq_add_neg,sub_sub_cancel]
 exact q _

end YM.CF.Bay
#print axioms YM.CF.Bay.goldCup
#print axioms YM.CF.Bay.pearlJet
