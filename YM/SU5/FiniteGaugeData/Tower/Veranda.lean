import YM.SU5.FiniteGaugeData.Tower.Helmsman
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
/-!
# Lattice arrangements of entries and relative reads in H_s time slabs

All time stamps physical packed in **integers** of the double step, registered on *this* ruler first. Reorders later. Membership/admissibility on input marks paid per fixed support and in placing x', so omit disjointness alone as requirement for commute (Fine-even central ALL supports at each fixed level, not D morphism on coincident). General semantics for read and rotations (q has full time and all coordinates).
-/
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C
local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "W"=>floorV Y H Q.circuit j 0 strict C
local notation "Φg" s:max v:max=>(S₀ s).gallery (look j) v
local notation "U" v:max=>relocate K j v
local notation "θ" x:max z:max=>mirror K x z
local notation "E₀" s:max i:max=>advance Y H V Q.circuit j 0 strict C (whenly (timeMesh Λ) s i)
local notation "Δ" v:max=>cad K (spare j (look j)) (gaea j v)
local notation "T" u:max=>transport Y H s j strict (look j) u
local notation "M" s:max f:max h:max=>boxOp Y H V s Q Qt j strict C _ f h
-- arbitrary local registrable marks (not yet limited to cov?)
abbrev observable (J:Calibration)(strict:Bool):= {p:Family J // TestFamily J true p ∧ (strict=true→ CovCover J p)}
/-- presentation of one arbitrary observable into an Entry for given axis. a shift η even code.
    Notice not changing j-spin base when using a *different* local registration. -/
structure Veranda (f:observable (tent Y H) strict) where -- fix
 rise: ℤ
 span : ℕ
 pos:0< span
 fwd : Entry Y H s j strict span
 yes : fwd.val.val= relocate (tent Y H) j rise f.val
noncomputable def Veranda.placed {f:observable (tent Y H) strict}(X:Veranda Y H s j strict f): (A).Op:= boxOp Y H V s Q Qt j strict C X.span X.fwd X.pos
-- room for any stencil on gauge lattice w buffer
lemma anyporch (f:observable (tent Y H) strict):Nonempty (Veranda Y H s j strict f):=by
 obtain ⟨S,p⟩:= f.property.1.paid; obtain ⟨d,t⟩:=Tower.sizes S; obtain ⟨x,t⟩:=t j
 let n:ℕ:=x.natAbs+(K).ℓ+1
 let Q:=plow K j n S; let Z:=ruler Λ.block; have ht:1 ≤ Z:=ruler_gene Λ.block
 let k:=2*n+x.natAbs+d
 have he : Between K j 0 (ruler Λ.block*k) Q :=by
    intro i u; obtain ⟨v,h,rfl⟩:=plow_stays K j n S u; specialize t v h; rw [moves,if_pos rfl]
    change 0+_ ≤v j+Z*n∧v j+Z*n+_≤ Z*k
    unfold k n; push_cast; have h:(x.natAbs:ℤ)=|x|:= Int.natCast_natAbs x;  obtain ⟨u,y⟩:=t; constructor
    · nlinarith [neg_le_abs x, mul_le_mul_of_nonneg_right ht (show 0≤|x|+ ((K).ℓ:ℕ)+1 by positivity)]
    nlinarith [le_abs_self x, mul_le_mul_of_nonneg_right ht (show 0≤2* |x|+ ((K).ℓ:ℕ)+(d:ℕ)+1 by positivity)]
 let x':= relocate K j n f.val
 have hy:InTest K true Q false x':=flow_port K j _ p
 let y:Γ s:=⟨x',(purpose_ok ..).2 ⟨(show _ from ⟨_,hy,by intro i v; rw [area0]; have h:= (he i v).1; simpa using h⟩),fun s=> chime_cov _ _ _ p (f.property.2 s)⟩⟩
 exact ⟨⟨n,k,by unfold k n; omega,⟨y,Q,hy,he⟩,rfl⟩⟩

variable {S:Type*}(X:S→ observable (tent Y H) strict)(Z : ∀i,Veranda Y H s j strict (X i))
local notation "Vs" l:max=> Veranda.placed Y H V s Q Qt j strict C (Z l)
-- clock realization of time-slot
include V C
lemma momentAct (v:ℕ)(f:Γ s):(S₀ s).Moment v ((κ s) f)=(κ s) (tick Y H s j 0 strict (2*v) f):=by
 change (E₀ s v) _=_; rw [advance_at,limited_time Y H V s Q.circuit j 0 strict C (2*v) le_rfl,amount_reset]
lemma transverseT (v:Trans j→ℤ)(f:Γ s):((T v) f).val=(Δ v) f.val:=transport_c Y H V s Q j strict C _ v f -- arguments? transported . uses V inclusion
lemma transverse_inverse (v:Trans j→ℤ)(x:Γ s): (T v) ((T (-v)) x)=x:=by
 apply Subtype.ext; rw [transverseT Y H V s Q j strict C,transverseT Y H V s Q j strict C]
 have hv:(gaea j v)+gaea j (-v)=0:=by funext i; simp only [Pi.add_apply, gaea]; split_ifs <;> simp
 have he:=(exam j _ K ((purpose_ok ..).1 x.property).1).1
 rw [cad_plus _ _ he,hv,cad_zero _ _ he]
variable (t:Cover) (h:ℕ) (f:S)
include Qt
lemma car_reads (x:Γ s):
 (S₀ s).personally (look j) (fun i=> t (i:Axis)) h (Vs f) ((κ s) x)= (κ s) (tick Y H s j 0 strict (2*h) ( (T (fun i=> t (i:Axis))) (slabT Y H s j strict _ (Z f).fwd ((T (-(fun i:Trans j=> t i))) x)))):=by
 unfold Console.personally; simp only [ContinuousLinearMap.comp_apply]; rw [transport_m,Veranda.placed,snatch_equal,transport_m,momentAct]

-- Relative operator semantics (no need inverse M identity across spacetime)
lemma paint (x:Γ s)(b:ℤ):
 (U b) (tick Y H s j 0 strict (2*h) ((T (fun i=>t (i:Axis))) (slabT Y H s j strict _ (Z f).fwd ((T (-(fun i:Trans j=>t (i:Axis)))) x)))).val =
 (U (b+h+(Z f).rise-t j)) (chart (tent Y H) t (X f).val) * (U (b+h+(Z f).span)) x.val:=by
 let z:=Z f; let i:=X f
 let v:Trans j→ℤ:=fun i=>t i
 let Tt := T v; let F:=spare j (look j)
 let T0:=T (-v)
 have he:=(exam j _ K ((purpose_ok ..).1 (T0 x).property).1).1
 change relocate _ _ _ (tick Y H s j 0 strict (2*h) (Tt (slabT Y H s j strict _ z.fwd (T0 x)))).val =
    _ * ((U (b+ (h:ℤ)+(Z f).span)) x.val)
 rw [timed_apply,show (Tt _).val=(Δ v) (slabT Y H s j strict _ z.fwd (T0 x)).val from transverseT Y H V s Q j strict C v _,slab_eq,cad_prod,z.yes,cad_movement _ j _ (i.property.1),cad_movement _ j _ he]
 rw [show cad K (spare j (look j)) (gaea j v) (T0 x).val=x.val from by rw [←transverseT Y H V s Q j strict C v (T0 x),transverse_inverse Y H V s Q j strict C]]
 repeat' rw [relocate_mul]
 rw [chart_piece K j _ i.property.1,transverse_eq K j _ _ v (fun _=>rfl)]
 have hx:=(cad_paid K (spare j (look j)) i.property.1 (gaea j v)); have hz:=(exam j _ K ((purpose_ok ..).1 x.property).1).1
 rw [relocate_sums K j _ _ hx,relocate_sums K j _ _ hx,relocate_sums K j _ _ hx,relocate_sums K j _ _ hz,relocate_sums K j _ _ hz,← add_assoc,← add_assoc (b:ℤ),sub_add_cancel]
section walk
variable [Fintype S]
noncomputable def score(p:S→ Cover)(l:List S): Family K:= (l.map (fun i=>chart K (p i) (X i).val)).prod
lemma scored (p:S→ Cover)(l:List S): TestFamily K true (score Y H strict X p l) :=by induction l with
 | nil=> exact aux_test (S:=∅) InTest.one
 | cons i t ih=> exact (cad_paid K _ (X i).property.1 _).mul ih
lemma score_eq(p:S→ Cover)(l v:List S)(α:l.Perm v):score Y H strict X p l=score Y H strict X p v:=by
 induction α with
 | nil=>rfl
 | cons k h ih => exact congrArg (chart K (p k) (X k).val * ·) ih
 | swap i u l=>
    let d i:= chart K (p i) (X i).val
    change d u* (d i* _)= d i* (d u * _); rw [←mul_assoc,←mul_assoc, show d u*d i=d i*d u from even_tests K (cad_paid K ordinate (X u).property.1 (p u)) (cad_paid K ordinate (X i).property.1 (p i))]
 | trans _ _ i j=> rw [i,j]
-- alignment from current time origin b: +T i plus veranda rise. recursion consume widths
def Weaves (p:S→ Cover)(Tq:S→ℕ):List S→ℤ→Prop
 | [],_=>True
 | i::L,b=> b+(Tq i:ℤ)+(Z i).rise=p i j∧ Weaves p Tq L (b+Tq i+(Z i).span)
local notation "woven"=> Weaves Y H s j strict X Z
local notation "personal" i:max t:max f:max=> (S₀ s).personally (look j) i t f
lemma lattice (p:S→ Cover)(Tq:S→ℕ)(l:List S)(b:ℤ)(hi:woven p Tq l b):
 let D₀ i:= fun k:Trans j=>p i k.val
 let q:= Average.ordered l (fun i=> (personal (D₀ i) (Tq i) (Vs i))) W
 ∃x:Γ s, q=(κ s) x ∧ (U b) x.val=score Y H strict X p l:=by
 dsimp only; induction l generalizing b with
 | nil=>
    exact ⟨unity Y H j 0 strict s,vacua Y H V Q.circuit j 0 strict C s, relocate_unit K j b⟩
 | cons i L ih=>
    obtain ⟨e,wv⟩:=hi
    obtain ⟨x,f,v⟩:= ih _ wv
    simp only [Average.orderly,f,car_reads Y H V s Q Qt j strict C X] -- tune X implicit
    refine ⟨_,rfl,?_⟩
    rw [paint Y H V s Q Qt j strict C, show b+ (Tq i:ℤ)+(Z i).rise-p i j=0 from by omega,relocate_zero K j (show TestFamily K true (chart K (p i) (X i).val) from cad_paid K _ (X i).property.1 _)]
    exact congrArg (fun v=>chart K (p i) (X i).val*v) v
-- align at head absolute clock n relative to its veranda. backF included arbitrary gap before head.
lemma attains (p:S→ Cover)(l:List S)(b:ℤ)(Tq:S→ℕ)(hi:woven p Tq l b):
 inner ℂ W (Average.ordered l (fun i=>personal (fun k:Trans j=>p i k.val) (Tq i) (Vs i)) W)=E s (score Y H strict X p l):=by
 obtain ⟨x,g,u⟩:=lattice Y H V s Q Qt j strict C X Z p Tq l b hi
 rw [g,← u,locates Y H V s Q Qt j strict C 1 (by decide)]
 have hx:= (exam j _ K ((purpose_ok ..).1 x.property).1).1
 exact (SWay Y H V s j (2*b) hx).symm
end walk
end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.attains
