import YM.SU5.LoomForce.LimitsFinger
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.LitCurrent.Surplus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical ContDiff
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{P T:SOp N}{a b d v g t u:ℝ}{r k:ℕ}
open Buffered Pannier.Chancel.Rous Next.Rank Spindle
variable {X:Seat N} (R:ℤ)
local notation "W"=> wrap (More N)
abbrev slipV (R:ℤ) := ((2:ℤ)*R) • (step 3:Cover)
abbrev haul (N:Side) (R:ℤ) := wrap (More N) (slipV R)
local notation "T₀"=> haul N R
local notation "Φ"=> fling 3 R N
local notation "j"=> Signed.mirror (3:Axis)
local notation "F"=> Next.Rank.Spindle.Turn
abbrev sendV (R:ℤ)(U:Face (Per (More N))):= Face.send (Signed.mirror 3) (haul N R) U
abbrev sendSite (X:Skye.Seat N) := affine (Signed.mirror 3) (haul N R) X
lemma tilt_rule : fling 3 R N=Lattice.pull (Signed.mirror 3) (haul N R):=by rw [fling_eq,haul,slipV,mul_smul]; rfl
abbrev realDir (i: PlaqAxes):ℝ:= if i.val.2=3 then -1 else 1
private lemma axis_ne (i:PlaqAxes): i.val.1≠3:=by
 intro p; have ht:=i.property; rw [p] at ht; have he:i.val.2 ≤ 3:=  (show ∀ x:Axis,x≤3 from by decide) i.val.2
 exact (not_lt_of_ge he ht)

private lemma side_shift(i:Axis)(p:i≠3) : (posDir i).rotate j=posDir i ∧ (negDir i).rotate j=negDir i:=by fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (p rfl)

variable (i:Face (Per (More N)))

lemma plazas : sendV R i= (if i.2.val.2=3 then sendSite R i.1-step (3:Axis) else sendSite R i.1,i.2) := by
 rcases i with ⟨x,⟨⟨i,y⟩,e⟩⟩; change i<y at e; let q:PlaqAxes:=⟨(i,y),e⟩; change Face.send j (haul N R) (x,q)= (if y=3 then (sendSite R x-step _) else sendSite R x,q)
 unfold Face.send Face.lower; change (atFace (sendSite R x) ((posDir i).rotate _) ((posDir y).rotate _), _ )=_; rw [(side_shift i (axis_ne q)).1]; have hp:PlaqAxes.rotate j q=q:=Subtype.ext (by change (min i y,max i y)= _; rw [min_eq_left e.le,max_eq_right e.le]); rw [hp]; split
 next h=>
    change y=3 at h; subst y; change ((sendSite R x+0)+- step (3: Axis),_)=_; rw [add_zero]; congr 1; abel
 next h=> rw [(side_shift y h).1]; unfold atFace; change ((sendSite R x+0)+0,_)=_; rw [add_zero,add_zero]

open Metric
lemma shuttle_stride(B: Pane N) : faceValue (Φ B) i = if i.2.val.2=3 then
    (B ((sendV R i).1,3))⁻¹ * (faceValue B (sendV R i))⁻¹ * B ((sendV R i).1,3) else faceValue B (sendV R i):=by
 rw [tilt_rule,plazas]
 rcases i with ⟨x,⟨⟨i,y⟩,g⟩⟩; change i<y at g; let q:PlaqAxes:=⟨(i,y),g⟩; let z:=sendSite R x; let w:=z-step (3:Axis); split
 next p=>
    change y=3 at p; subst y; rw [faceValue,travel_pull];
    rw [show ((square i 3).map (fun s=>s.rotate j)) = oriented (posDir i) (negDir 3) from ?_]; swap
    · simp only [square,List.map_cons,List.map_nil, (side_shift i (axis_ne q)).1,(side_shift i (axis_ne q)).2]; rfl
    change travel B z (oriented (posDir i) (negDir 3))=(B (w,3))⁻¹ * (travel B w (oriented (posDir i) (posDir 3)))⁻¹ *_
    rw [oriented_swap (posDir 3) (posDir i)];
    have he:w+(posDir 3).vec=z:= sub_add_cancel ..; have h':= oriented_next (posDir 3) (posDir i) w B; rw [he] at h'
    rw [inv_inv]; exact h'
 next p=>
    rw [faceValue,travel_pull]; change travel _ z ((square i y).map fun s=> s.rotate j)= travel _ z (square i y); rw [show ((square i y).map fun s=> s.rotate j)= square i y from (by simp only [square,List.map_cons,List.map_nil,(side_shift i (axis_ne q)).1,(side_shift i (axis_ne q)).2,(side_shift y p).1,(side_shift y p).2])]
lemma handReflect (b:Seat N)(p:PlaqAxes)(t:p.val.2=3) : b+step (3:Axis) ∈ touched (b,p) := by
 unfold touched; apply List.mem_toFinset.mpr; unfold square visits; dsimp
 simp_rw [t]; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; simp only [Step.vec_pos,Step.vec_neg]; rw [show b+step p.val.1+step 3+-step p.val.1=b+step 3 by abel]; exact List.Mem.head _

variable (B:ℕ) (o:Seat N)
local notation "A"=> FrameA B
local notation "Z"=> Spindle.patch B o
local notation "Σ"=>Turn B
abbrev stationary (T:Signed)(b:Seat N)(i:F B): Face (Per (More N)):= Face.send T b (armFace B o i)
def reflected (t:ℤ)(U:Pane N) : FrameA B := fun i=> (realDir i.val.2) • group.curvature (faceValue U (sendV t (armFace B o i)))
-- supports precise. Yield pointwise price even though later use full cube pricing.
lemma bounded_reflect (b:Spindle.Turn B)(U:Pane N)(w:Tiny ((Spindle.patch B o).image (sendSite R)) U u)(u':0≤u)(t':0 ≤ t)
    (p:Healthy t (Spindle.patch B o) (Φ U)) : ‖reflected B o R U b‖ ≤ t ∧ ‖receiveMark B o (Φ U) 1 b‖ ≤ t ∧
      ‖receiveMark B o (Φ U) 1 b -reflected B o R U b‖ ≤ 2*group.colorScale*u*t:=by
 let V : Face (Per (More N)):= armFace B o b; let k:= sendV R V; let tQ:=faceValue U k
 have he:group.chord (faceValue (Φ U) V)≤t:=by
    refine le_of_not_gt (fun w=>Finset.disjoint_left.mp p (touches B o b (Work.E01.base_touched _)) ((flags_spec ..).2 ⟨V,Work.E01.base_touched _,w⟩))
 rw [tilt_rule R] at he -- price eq
 rw [Face.send_price U V j T₀ group.chord group.chord_inv (fun k g=> Gauge.chord_conj ..)] at he
 have ht: ‖group.curvature tQ‖≤ t:= (Gauge.curvature_norm ..).trans he
 have hm: touched k ⊆ (Spindle.patch B o).image (sendSite R):= (Work.H03.touched_send j T₀ V) ▸ image_subset_image (touches B o b) -- maybe
 unfold reflected receiveMark; rw [one_smul, shuttle_stride];
 let a:= group.curvature tQ; change ‖realDir b.val.2 • a‖ ≤ t∧‖group.curvature _‖ ≤ t ∧ ‖group.curvature _-realDir b.val.2 • a‖ ≤ _
 unfold realDir; change _∧‖group.curvature (if b.val.2.val.2=3 then (U (k.1,3))⁻¹ *tQ⁻¹*U (k.1,3) else tQ)‖≤ _ ∧ _
 split_ifs with p'' u'' hu'
 all_goals try contradiction
 · let i:Edge (Seat N):=(k.1,3); let θ:=U i; let X:= θ⁻¹*tQ⁻¹*θ
   have Hp: tQ=faceValue U k:=rfl
   have Hc: group.curvature X = group.adjoint θ⁻¹ (-a) := by
     rw [show (-a)=group.curvature tQ⁻¹ from (Gauge.curvature_inv ..).symm, ← Gauge.curvature_conjugate,inv_inv]
   have H': group.chord θ⁻¹≤u:= by
     rw [Gauge.chord_inv]; apply w i (hm (Work.E01.base_touched k)); refine hm (handReflect k.1 k.2 ?_)
     unfold k; rw [plazas]; exact u''
   have he:= group.colorScale_pos
   simp only [neg_one_smul,norm_neg]; change ‖a‖≤_ ∧ ‖group.curvature X‖≤ _ ∧ ‖group.curvature X - -a‖≤ _; rw [Hc,Gauge.norm_adjoint,norm_neg]; refine ⟨ht,ht, (Next.Fluctuations.adjoint_norm_sub ..).trans ?_⟩; rw [norm_neg]; gcongr
 simp only [one_smul]; refine ⟨ht,ht,?_⟩; change ‖a-a‖ ≤ _; rw [sub_self,norm_zero]; have he:= group.colorScale_pos; positivity
#print axioms bounded_reflect
end YM.CF.LitCurrent.Surplus
