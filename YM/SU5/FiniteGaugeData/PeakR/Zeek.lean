import YM.SU5.FiniteGaugeData.PeakR.Prat
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
open Largo Chaperone
namespace Corners
set_option quotPrecheck false
variable {N:Side}{o a b x y:Cover}
section geometry
variable (N:Side)(p q:ℕ)
variable {p q}
variable (b0:Bool)(l:ℕ)
def stagePr (p q l:ℕ)(b0:Bool) : Finset Cover:= (estate p q).filter fun i=> ∀ a:Axis, (l:ℤ) ≤ if b0 then i a else -i a
lemma stage_hi(b:Bool){V: Cover} : V∈stagePr p q l b → ∀ i:Axis,(l:ℤ)≤ if b then V i else -V i:=fun h=> (mem_filter.mp h).2
lemma highAhead (a:Axis) : Ahead a 0 l (stagePr p q l true):=fun x h=> (zero_add (l:ℤ)).symm ▸ stage_hi l true h a
lemma refS (a:Axis) : Ahead a 0 l (refract a 0 (stagePr p q l false)):=by
 intro x y; obtain ⟨x,p',rfl⟩:=mem_image.mp y; have he:= (show (l:ℤ) ≤ -x a from stage_hi l false p' a); rw [zero_add, fling_move,if_pos rfl]; omega
lemma stage_disj (v:0<l) : Disjoint (stagePr p q l false) (stagePr p q l true):=by
 refine Finset.disjoint_left.mpr fun i h p=>?_ ; have he:=(show (l:ℤ) ≤ -i 3 from stage_hi _ _ h 3); have hp:=(show (l:ℤ) ≤ i 3 from stage_hi _ _ p 3); omega
lemma floor₃ (t:BetweenY a o b)(u:a∈stagePr p q l b0)(v:b∈stagePr p q l b0): o∈stagePr p q l b0:=by
 refine mem_filter.mpr ⟨convexTown ((mem_filter.mp u).1) ((mem_filter.mp v).1) t,fun j=>?_⟩; have ht:=t.left j; have hh:= t.right j; have hp:= stage_hi l b0 u j; have hg:=stage_hi l b0 v j; cases b0 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
-- chart using order. arbitrary roots.Price orientation exact. L->R. need H. BENT (branch) chart.
abbrev pegT (l:ℕ)(b0:Bool):Cover:= fun i=> if b0 then l else -(l:ℤ)
lemma pegT_here (e:l≤p)(v:l≤q): pegT l b0∈ stagePr p q l b0:=by
 refine mem_filter.mpr ⟨?_,?_⟩
 · apply (own _).mpr; intro i; unfold pegT zoneL; by_cases t:i=3 <;> cases b0 <;> simp only [t, ↓reduceIte, Bool.false_eq_true] <;> omega
 unfold pegT; cases b0 <;> simp
def limbP (o:Cover): Chart o where
 τ i:= route o i 1
 endsT i:= route_end ..
lemma limbR (e:o∈stagePr p q l b0): Chart.Hires (stagePr p q l b0) (stagePr p q l b0) o (limbP o):= fun i t x v=> floor₃ b0 l (axis_travel o i x (List.mem_toFinset.mp v)) e t
local notation "Y"=> stagePr p q l false
local notation "Φ"=> stagePr p q l true
local notation "yL"=> pegT l false
local notation "yR"=> pegT l true
def Line (p q:ℕ)(l:ℕ): Chart (pegT l true) where
 τ i:= if i∈stagePr p q l false then route (pegT l true) (pegT l false) 1++(limbP (pegT l false)).τ i else route (pegT l true) i 1
 endsT x:=by split <;> simp [stop_append,route_end,limbP]
private lemma backer (P:a∈estate p q)(Q:b∈estate p q)(x:Cover)(h:x∈ visits a (route a b 1)): x∈estate p q:=convexTown P Q (axis_travel a b x h)
variable {u v:ℕ}
lemma Line_area (e:l≤ p)(z:l≤q)(u0:p≤u)(v0:q≤v): Chart.Hires (estate u v) (estate u v) (pegT l true) (Line p q l):=by
 intro i h x t; let g:= limbP; have hx:= List.mem_toFinset.mp t; change x∈visits yR (if i∈Y then _ else _) at hx; have hP(b):pegT l b∈estate u v:=ownM u0 v0 ((mem_filter.mp (pegT_here (q:=q) b l e z)).1); split at hx; next v =>
    rcases append_visit hx with p|p; exact backer (hP true) (hP false) x p
    rw [route_end] at p; exact backer (hP false) h x p
 next v=> exact backer (hP true) h x hx
section
variable {T:Finset Cover} (p₀:Hosp T N)(q₀:estate p q⊆ T)
local notation "L"=> region (stagePr p q l false) N
local notation "R"=> region (stagePr p q l true) N
-- Frame proof. F₀.Own.
open Window.Mirage
variable (t:0<l)(e:l≤p)(z:l≤q)
abbrev cornerD(b:Bool):= Chart.passH (limbP (pegT l b)) p₀ (show stagePr p q l b⊆T from fun i z=> q₀ ((mem_filter.mp z).1)) (limbR b l (pegT_here b l e z)) -- U ambiguous same
-- Line.Extend.Pith.
include t
lemma CurveF (Q:Chart.Hires (estate p q) T (pegT l true) (Line p q l)) : Mirage.Frame (cornerD N l p₀ q₀ e z false) (cornerD N l p₀ q₀ e z true) (Chart.passH (Line p q l) p₀ q₀ Q):=by
 constructor
 · intro a; let k:= travel (onC N a) yR (route yR yL 1); refine ⟨k,fun i h=>?_⟩; have h0: Chart.legH N T i∈ stagePr p q l false:=by obtain ⟨x,u,rfl⟩:=mem_image.mp (show i∈ L from h); rw [Chart.leg_on p₀ x (q₀ ((mem_filter.mp u).1))]; exact u
   unfold cornerD Chart.passH Chart.tenor Chart.rootF Line; dsimp only; rw [if_pos h0, travel_append,route_end]; rfl
 intro a x h; have hy:Chart.legH N T x∉stagePr p q l false:=by obtain ⟨x,u,rfl⟩:=mem_image.mp (show x∈ R from h); rw [Chart.leg_on p₀ x (q₀ ((mem_filter.mp u).1))]; exact fun e=> Finset.disjoint_left.mp (stage_disj l t) e u
 unfold cornerD Chart.passH Chart.tenor Chart.rootF Line; dsimp only; rw [if_neg hy]; rfl
end
end geometry
open ArchiveK.Midway
lemma helix_cut {n:ℕ}{x:Cover}(p:x∈Lattice.box n) : nodeC x∈ WoodV (helix n) (helix n):=by
 rw [WoodV,own]; intro i; obtain ⟨v,w⟩:= box_test.mp p; unfold helix zoneL; rw [ite_self]; simp only [nodeC,Pi.add_apply, two_smul, Pi.one_apply]; specialize w i; specialize v i; omega
lemma helix_stage (b:Bool)(l:ℕ){n:ℕ}(x:0<l) {S:Finset Cover}(U:S⊆ Lattice.box n)(t:Land b l S): S.image nodeC⊆stagePr (helix n) (helix n) l b:=by
 intro i z; obtain ⟨u,q,rfl⟩:= mem_image.mp z; refine mem_filter.mpr ⟨helix_cut (U q),fun i=>?_⟩; have he:=t u q i; unfold nodeC; simp only [Pi.add_apply,two_smul,Pi.one_apply]; cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at *<;> omega
-- powers.v ≤ helm.Price buy diagonal.Budget.x new annotation.
open Hierarchy.Eight
lemma sphereΞ (K:Calibration)(n d J:ℕ):capR K (fun _=>2*(ceilT n d J))=expanse n d J (addgap K):= Hierarchy.Eight.sphereCap .. -- tune namespace
lemma manorL (n d J:ℕ) (i:Axis) : ∃ t:ℤ, film t (2*ceilT n d J) (Manor (helix n) (helix n) d J) i:=by
 let R:= ceilT n d J; refine ⟨-(R:ℤ),fun u t=> ?_⟩; -- film.Local
 have hp:=  (own u|>.1 t) i; unfold zoneL at hp; rw [ite_self] at hp; unfold R ceilT; omega -- syntax binder
#print axioms CurveF
end Corners
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
