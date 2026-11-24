import YM.SU5.FiniteGaugeData.Tower.Synergy
import YM.SU5.FiniteGaugeData.Tower.BoxWorks
/-!
# Whole group movement at one rung

Interprets the last-tech ergodic calculators on the current H, no tilts or
prelimit integrals. Further identification using saturated widths on frozen
subspaces. All expected values keep on same E and ∀ aligned axes.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
section allmove
variable (K:Calibration)
local notation "S" i:max x:max=> relocate K i x
lemma commZ (a b:Axis)(x y:ℤ){f:Family K}(p:TestFamily K true f): (S a x) ((S b y) f)=(S b y) ((S a x) f):= twin_slide a b _ _ p.paid.choose_spec
def cad (l:List Axis)(v:Cover)(x:Family K):Family K:=l.foldr (fun i y=> relocate K i (v i) y) x
local notation "A" y:max=>cad K y
variable {x y:Family K}(i:Axis)(l:List Axis)
lemma cad_step(v:Cover): (A (i::l)) v x=(S i (v i)) ((A l) v x):=rfl
lemma cad_paid (p:TestFamily K true x)(v:Cover): TestFamily K true ((A l) v x):=by induction l with
 | nil=>exact p
 | cons i l a=> exact move_ok K i _ a
lemma cad_movement (p:TestFamily K true x)(v:Cover)(z:ℤ): (A l) v ((S i z) x)=(S i z) ((A l) v x):=by
 induction l with
 | nil=>rfl
 | cons t l a=> rw [cad_step,cad_step,a,commZ K _ _ _ _ (cad_paid K l p _)]
lemma cad_plus(p:TestFamily K true x)(v w:Cover):(A l) v ((A l) w x)=(A l) (v+w) x:=by
 induction l generalizing x with
 | nil=>simp only [cad,List.foldr_nil]
 | cons t l a=>
    simp only [cad_step]; rw [cad_movement K t l (cad_paid K l p _),Pi.add_apply,a p,relocate_sums K t _ _ (cad_paid K l p _)]
lemma cad_prod (v:Cover): (A l) v (x*y)=(A l) v x*(A l) v y:=by induction l with
| nil=>rfl
| cons t l ih=>rw [cad_step,cad_step,cad_step,ih,relocate_mul]
lemma cad_zero(p:TestFamily K true x):(A l) 0 x=x:=by induction l with
| nil=>rfl
| cons t l ih=>rw [cad_step,ih,Pi.zero_apply,relocate_zero K t p]
lemma cad_perm {p':List Axis}(a:l.Perm p')(h:TestFamily K true x)(v:Cover):cad K l v x=cad K p' v x:=by
 induction a with
 | nil=>rfl
 | cons i _ ih => rw [cad_step,cad_step]; congr 1
 | swap i j t=> exact commZ K j i (v j) (v i) (cad_paid K t h _)
 | trans _ _ a b=>rw [a,b]
noncomputable def ordinate:List Axis:= Finset.sort univ (· ≤ ·)
lemma ordinates(i:Axis): i∈ordinate:=by simp [ordinate]
lemma ordinate_one:ordinate.Nodup:= Finset.sort_nodup ..
def chart(v:Cover):=cad K ordinate v
def spare(v: Axis)(x: List (Trans v)):List Axis:=x.map (fun i=>i.val)
lemma normal(j:Axis): List.Perm ordinate (j::spare j (look j)) := by
 have hn:(j::spare j (look j)).Nodup:=by
    refine List.nodup_cons.mpr ⟨fun h=>?_,(look_one j).map Subtype.val_injective⟩
    obtain ⟨i,t,g⟩:=List.mem_map.mp h; exact i.property g
 rw [List.perm_ext_iff_of_nodup ordinate_one hn]
 intro i; refine ⟨fun _=>?_,fun _=>ordinates _⟩
 rcases eq_or_ne i j with rfl|p
 · exact List.Mem.head ..
 exact List.Mem.tail _ (List.mem_map.mpr ⟨⟨_,p⟩,look_all _ _,rfl⟩)
noncomputable def gaea(j:Axis)(x:Trans j→ℤ)(i:Axis):ℤ:= if h:i=j then 0 else x ⟨i,h⟩
-- time x j plus transverse chart. no need mask lemma
lemma chart_piece (j:Axis)(v:Cover)(h:TestFamily K true x): chart K v x=(S j (v j)) (cad K (spare j (look j)) v x):= (cad_perm _ ordinate (normal j) h v).trans rfl
lemma transverse_eq (j:Axis)(t:List (Trans j))(p:Cover)(w:Trans j→ℤ)(h:∀i:Trans j,p (i:Axis)=w i):cad K (spare j t) p x=cad K (spare j t) (gaea j w) x:=by induction t with
| nil=>simp only [cad,spare,List.map_nil,List.foldr_nil]
| cons i t ih=> rw [show spare j (i::t)= (i:Axis)::spare j t from rfl,cad_step,cad_step,ih,h i]; congr 2; unfold gaea; rw [dif_neg i.property]

end allmove
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C
local notation "Ε"=>advance Y H V Q.circuit j 0 strict C
local notation "B" s:max f:max h:max=>boxOp Y H V s Q Qt j strict C _ f h
local notation "Φ" b:max x:max=> ((ladder Y H V Q.circuit j 0 strict C).crew b).play x
local notation "M"=>timeMesh Λ
open MeshClock SlabMark OS.Semigroup Germ
include V C
lemma roots(n:ℕ)(v:Cover){fA:Family (tent Y H)}(p:TestFamily K true fA) : E n (chart K v fA)=E n fA:=by
 unfold chart; generalize ordinate=s
 induction s with
 | nil => rfl
 | cons j l ih=> rw [cad_step]; exact (SWay Y H V n j (2*v j) (cad_paid K l p v)).trans ih
-- Grid jams at one refinement. E clock NNReal fixed.
noncomputable def office : Console (Trans j) A where
 move b:={
    wind z:= Φ b (MeshClock.notch M s z)
    nil:=by rw [notch_zero]; exact Germ.Players.play_zero _
    small i:=by rw [on_ladder]; exact sailV_small .. -- tune
    along u v:=by rw [Germ.Players.piles, notch_add] }
 separate i k x y:= Germ.Alliance.cCom (ladder Y H V Q.circuit j 0 strict C) _ _ _ _
 Moment n:= Ε (MeshClock.whenly M s n)
 shrinking n:=advance_small ..
 rise:=by rw [when_zero,advance_source]
 steady := let t:= (clockdrive Y H V Q.circuit j 0 strict C).monoAxis j
           t.orth
 wave i:=by
    let t:= (clockdrive Y H V Q.circuit j 0 strict C).monoAxis j
    have he:Tendsto (MeshClock.whenly M s) atTop atTop:=by unfold whenly; apply Filter.Tendsto.atTop_mul_const (mill_pos M s) tendsto_natCast_atTop_atTop -- Nonneg not ordered ring lemma?
    exact (t.emerges i).comp he
 flip i b v:= (ladder_time Y H V Q.circuit j 0 strict C b _ (notch M s v)).symm

local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "F"=> floorV Y H Q.circuit j 0 strict C
local notation "Φg" s:max v:max=> (S₀ s).gallery (look j) v

lemma occupant (v:Trans j→ℤ): (Φg s v) F=F:=by
 generalize look j=T
 induction T with
 | nil=>rfl
 | cons i t ih=> rw [Moving.entry,ContinuousLinearMap.comp_apply,ih]; change (Φ i (notch M s (v i))) F=F; rw [on_ladder,sailV_vac]
lemma momentF(x): (S₀ s).Moment x F=F:=advance_vacuum ..
lemma backF(x)(i:A): inner ℂ F ((S₀ s).Moment x i) =inner ℂ F i:=by
 change inner ℂ F ((Ε _) i)= _; rw [← advance_adjoint Y H V Q.circuit j 0 strict C,ContinuousLinearMap.adjoint_inner_right,advance_vacuum]
noncomputable def transport (t:List (Trans j))(v:Trans j→ℤ)(x:Γ s):Γ s:= t.foldr (fun (i:Trans j) y=> sail Y H s j 0 strict (i:Axis) i.property (2*v i) y) x
lemma transport_m (t: List (Trans j)) (v:Trans j→ℤ)(x:Γ s):
 (S₀ s).gallery t v ((κ s) x)=(κ s) (transport Y H s j strict t v x):=by
 induction t with
 | nil=>rfl
 | cons i t ih=>
    rw [Moving.entry,ContinuousLinearMap.comp_apply,ih]; change (Φ i _) _=_; rw [on_ladder,sailV_at Y H V _ Q.circuit j 0 strict i.val i.property C (2*v i) s le_rfl,smill_id]; rfl
lemma transport_c (t:List (Trans j)) (v:Trans j→ℤ)(x:Γ s):
 (transport Y H s j strict t v x).val=cad K (spare j t) (gaea j v) x.val:=by induction t with
| nil=> rfl
| cons i t ih=>rw [transport,List.foldr_cons]; simp only [spare,List.map_cons,cad_step]; change chime K i.val _ ((transport Y H s j strict t v x).val)= _; rw [ih]; unfold relocate; congr 2; rw [gaea,dif_neg i.property]
 
end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.occupant
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.cad_perm
