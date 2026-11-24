import YM.CF.BPress.Hazel.Harbor
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth}{u v γ : ℝ} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch
private lemma diag_bridge {d r:ℕ} {E:Type*} (f:Space d s→E)(x:Space d s)(u:∀ i j, delta x i≤ r → delta x (Grid.hop i j 1) ≤ r → f i=f (Grid.hop i j 1)) (v w)(p:delta x v≤r)(q:delta x w≤r)(e:delta v w≤1) : f v=f w:=by
 let F(A:Finset (Fin d))(i:Fin d):=if i∈A then w i else v i; have he(A):delta x (F A)≤ r:= delta_le.mpr (fun i=>by unfold F; split; exact (delta_at ..).trans q; exact (delta_at ..).trans p); have hz(A:Finset (Fin d)){i:Fin d}(t:i∉A) : f (F (insert i A))=f (F A):=by
    let a:= F A; let b:= F (insert i A); have ht: delta1 s (b i) (a i)≤1:=by simp only [b,a,F,t,mem_insert_self, ↓reduceIte]; exact (d_sym ..).le.trans ((delta_at v w i).trans e)
    have hV(j)(g:j≠i):b j=a j:=by simp [a,b,F,g]
    obtain ⟨n,p,h⟩:=step_exists _ _ _ ht; have p:n=0∨n=1∨n= -1:=by omega
    rcases p with p|p|p <;> rw [p] at h; exact congrArg f (show b=a from funext fun j=>by by_cases v:j=i; subst j; simpa using h; exact hV _ v); have hh:b=Grid.hop a i 1:=funext fun j=>by by_cases v:j=i; subst j; simpa using h; simpa only [hop_diff a i j v] using (hV j v)
    rw [← show b=F (insert i A) from rfl,←show a=F A from rfl,hh]; exact (u a i (he A) (by rw [←hh]; exact he _)).symm; -- tune after
    have ht:a=Grid.hop b i 1:=funext fun j=>by by_cases v:j=i; subst j; rw [hop_same,h]; simp [add_assoc]; simpa only [hop_diff b i j v] using (hV j v).symm
    rw [← show a=F A from rfl,←show b= F _ from rfl, ht]; exact u b i (he _) (ht ▸ he A) -- tune
 have hf(A:Finset (Fin d)): f (F A)= f v:=by induction A using Finset.induction with|empty=> simp [F]| insert i A k ih=> exact (hz A k).trans ih
 rw [← hf univ]; simp [F]
lemma axial_same {d r:ℕ}{E:Type*} (f:Space d s→E)(x:Space d s)(u:∀ i j, delta x i≤ r → delta x (Grid.hop i j 1) ≤ r → f i=f (Grid.hop i j 1)) {v:Space d s} (t:delta x v≤r): f x=f v:=by
 induction r generalizing v with
 | zero => rw [eq_of_delta x v (Nat.eq_zero_of_le_zero t)]
 | succ n ih=> obtain ⟨z,t',h⟩:=decrease_bay x v t; exact (ih (fun i j p q=> u i j (p.trans (Nat.le_succ _)) (q.trans (Nat.le_succ _))) t').trans (diag_bridge f x u z v (t'.trans (Nat.le_succ _)) t h)

variable {X:Bands s B}{R:Hangar s}{T:Seal (SiteX X R)}
def stable (g:X.Hcols→Fin 5) (R:Hangar s)(T:Seal (SiteX X R)) := ∀ (v:X.Index) (x:Tri s)(i:SpatialDir), Good X R T 2 (v,x)→ Good X R T 2 (v,glide i x) → g (v,x)=g (v,glide i x)
variable {g:X.Hcols→Fin 5}
lemma staysWith {x₁ x₂:X.Index}{a b:Tri s} (h:stable g R T)(t:x₁=x₂)(v:delta a b≤ R.L.val)(p:Good X R T 3 (x₁,a)): g (x₁,a)= g (x₂,b):=by
 subst x₂; apply axial_same (fun x=>g (x₁,x)) a _ v; intro i j h' q; rw [hop_glide] at *; exact h x₁ i j (good_cc p rfl (show delta a i≤R.L.val from h')) (good_cc p rfl (show delta a (glide j i)≤R.L.val from q)) -- tune x
lemma carriedP {x y:X.Hcols}(h:stable g R T)(p:Good X R T 3 x)(u:x.1=y.1)(v:delta x.2 y.2 ≤ R.L.val):g x=g y:= staysWith h u v p
lemma brake (h:stable g R T)(i:Link s)(p: Good X R T 2 (Locale.panel X i.1))(q: Good X R T 2 (Locale.panel X (endAt i)))(t:town X i.1=town X (endAt i)): g (panel X i.1)= g (panel X (endAt i)):=by
 rcases link_cases i with ⟨x,l⟩|l <;> rw [l] at t q p ⊢
 · simp only [endAt,fl,event_across,am_event] at *; exact h _ _ _ p q
 simp only [endAt,vl,event_up,am_event] at *; apply congrArg; exact Prod.ext t rfl -- tune
end YM.CF.BPress.Hazel
