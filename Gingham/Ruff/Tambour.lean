import Gingham.Ruff.Sheaf
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry


open Tower SlabMark
variable {K:Calibration}

lemma sunriseV {p:BudgetPoint}{C:ℝ}{l:Bool}{m N:Side}
   (h:K.c m=N){F:Mark N}
   (v:Opening p C l F)(r:Roomy (wisp p) N):
   ∃z:Swatch (wisp p),
     z∈LitRose (wisp p) K p C l ∧
     Tapestry.arrange _ _ h (render (wisp p) K z m) = F:=by
    subst N; exact sunrise (le_rfl) r v

structure Pleiad (K:Calibration)(p:BudgetPoint)(C:ℝ)
       (F:Fleece K): Prop where
  train(l): Bouquet (wisp p) C (leafpure l) (F l)
  fidelity(l):
    ∃ x:Option ℕ →Swatch (wisp p),
      (∀ i,x i∈LitRose (wisp p) K p C (leafpure l)) ∧
      Tendsto (x∘some) atTop (𝓝 (x none)) ∧
      ∀ i,render (wisp p) K (x i)= F l i

variable
  {p:ℕ→BudgetPoint} {C:ℝ} {N m:ℕ→ℕ→Side}
  (good:ℕ→ℕ→Prop)
  (Y:∀s n, good s n→Leaf→Mark (N s n))
  (q:∀s n,K.c (m s n)=N s n)
theorem Flora_picks
  (v:∀s n, ∀h:good s n,
      ∀l, Opening (p s) C (leafpure l) (Y s n h l))
  (r:∀s n,good s n→ Roomy (wisp (p s)) (N s n))(c:0≤C):
 ∃ (ν:ℕ→ℕ) (F:ℕ→Fleece K), StrictMono ν ∧
   (∀s,Pleiad K (p s) C (F s))∧
   ∀s n, ∀h:good s (ν n), ∀l,
     Tapestry.arrange _ _ (q s (ν n))
       (F s l (some n) (m s (ν n)))= Y s (ν n) h l :=by
  have y(n:ℕ)(a:ℕ × Leaf):
      ∃z:Swatch (wisp (p a.1)),
         z∈LitRose (wisp (p a.1)) K (p a.1) C (leafpure a.2) ∧
         ∀h,Tapestry.arrange _ _ (q a.1 n) (render _ K z (m a.1 n))
            =Y a.1 n h a.2:= by
    by_cases t:good a.1 n
    · obtain ⟨x,b,e⟩:=sunriseV (q a.1 n) (v _ _ t a.2) (r _ _ t)
      exact ⟨x,b,fun _=>e⟩
    exact ⟨0,rose_origin _ _ _ _ _ _ c (mul_nonneg c (ali_nonneg _)),fun h=>False.elim (t h)⟩
  choose z u h using y
  obtain ⟨ν,x,a,b,e,w,t⟩:=gardens (K:=K)
    (S:=fun p':ℕ×Leaf=> wisp (p p'.1))
    (U:=fun a=>flash (p a.1))
    (C:=fun _=>C)
    (D:=fun a=> C*aliquot (wisp (p a.1)))
    (H:=fun a=>leafpure a.2) (fun _=>c) (fun i=>mul_nonneg c (ali_nonneg _)) z u
  refine ⟨ν,fun s l n=>render _ K (x (s,l) n),a,
     fun s=>⟨fun l=>t (s,l),fun l=>⟨x (s,l),fun i=>b (s,l) i,w (s,l),fun i=>rfl⟩⟩,?_⟩
  intro s n f l
  dsimp only
  rw [e n (s,l)]
  exact h _ (s,l) _

#print axioms Flora_picks

lemma posed_receipt {u:Side}{F:Fleece K}{M T:Side}(e:K.c M=T)
  (t:ruler K.B=2*(u.val:ℤ)){D:Leaf→Mark T}
  {o:Option ℕ}
  (p:∀l,Tapestry.arrange _ _ e (F l o M)=D l)
  (word:List (Axis×ℤ))(y:ℝ):
  Tapestry.arrange _ _ e
    (Dancing word (wingtip (y:ℂ) F) o M)=
      (y:ℂ) • maiden word (GarlandBook.vase u (D none)
              (fun i=>D (some i))):=by
  subst T
  replace p:(fun l=>F l o M)=D:=funext p
  change maiden word (wingtip (y:ℂ) F o M)=_
  rw [wing_receipt t,pose_scaled,←p]

