import YM.CF.BProof.Mapping.Read

/- local reads of moods and lift, not assuming level accepted. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Face
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable (K:Chart G) (y:ℝ){s:Side}(U V:Sheet s)(p:Space s)(h: ∀ i,read U p i=read V p i)
include h
lemma tilt_read : tilt K y U p=tilt K y V p:= PiLp.ext fun i=> by change _ • slog _ _=_ • slog _ _; rw [h i]
lemma orient_read (t:Fin 5) : orient K y U p t=orient K y V p t:=by
 have he:= tilt_read K y U V p h; have hf(i): label K y U p i=label K y V p i:=by unfold label; rw [he]
 have hh : nearIndex K y U p=nearIndex K y V p:= by
   let x(A:Sheet s): Finset (Fin 5):= univ.filter fun i=> nearest K y A p i; have hx:x U=x V:= by ext i; simp [x,nearest,hf]
   change (x U).min' (best_v K y U p)=(x V).min' (best_v K y V p); exact (by congr 1)
 unfold orient; rw [hh,hf]
lemma mood_read (t:SU.group.El): Mood K y U p t=Mood K y V p t:=by unfold Mood inChart; simp only [tilt_read K y U V p h,h]
end YM.CF.BProof.Face
namespace YM.CF.BProof.Mapping.Pawn
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House
open Gauss Release Release.hot
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}{Y:Yard s}(g:Ratio c s)(S:Hall s)
variable (x y: Pawn Y)(Z: Finset (Block Y c))(z:ℝ)(T:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U:Beam c' R Y.short M z)
variable (h:Charge.Room Y M)(u:Agreed g x y Z) {i:Y.Index}(k:¬Y.D i)(b: Bool)(p:Space s)(r:TAxis)
private lemma slide_n : (Gauss.base Y).N (location Y i b,p) (location Y i b,p+tstep r) 1:= ⟨rfl,(Face.slide_t ..) ▸ Grid.near_slide p r⟩ -- tune
include h u k
lemma face_eq (v: Shade g Z (location Y i b,p) U.horizon') : inlet (Y.u i) Y.long (issue x z T θ U) b (p,r)=inlet (Y.u i) Y.long (issue y z T θ U) b (p,r):=by rw [x.paid,y.paid, local_level g x y Z z T θ U h _ u v]; exact k; exact k
lemma square (v:Shade g Z (location Y i b,p) (1+U.horizon')) (r:TAxis): Face.read (inlet (Y.u i) Y.long (issue x z T θ U) b) p r = Face.read (inlet (Y.u i) Y.long (issue y z T θ U) b) p r:=by
 let a:=location Y i b; let f(j):= inlet (Y.u i) Y.long (issue j z T θ U) b
 have hp (x':Space s)(t)(u':Grid.dist p x' ≤1) : f x (x',t)= f y (x',t):= face_eq g x y Z z T θ U h u k b x' t (shade_rides g Z v (show (Gauss.base Y).N (a,p) _ 1 from ⟨rfl,u'⟩))
 have H:Grid.dist p p≤1:=by simp
 have K(i):Grid.dist p (p+tstep i) ≤1:= (Face.slide_t ..) ▸ Grid.near_slide p i; change Face.read (f x) p r=Face.read (f y) p r; unfold Face.read; dsimp only; rw [hp p _ H,hp _ _ (K _),hp _ _ (K _),hp p _ H] -- tune
lemma signs (p:Space s)(v:Shade g Z (location Y i b,p) (1+U.horizon')): x.rent S z T θ U i b p=y.rent S z T θ U i b p:=by
 unfold rent sweepLabel peeks; rw [if_neg k,if_neg k]; rw [u.mood i b p k (shade g Z _ _ v)]; exact Face.orient_read S.K z _ _ p (square g x y Z z T θ U h u k b p v) _
lemma ticket_mood (p:Space s)(v: Shade g Z (location Y i b,p) (1+U.horizon')): Face.Mood S.K z (inlet (Y.u i) Y.long (issue x z T θ U) b) p (x.rent S z T θ U i b p)= Face.Mood S.K z (inlet (Y.u i) Y.long (issue y z T θ U) b) p (y.rent S z T θ U i b p):=by
 rw [signs g S x y Z z T θ U h u k b p v,Face.mood_read _ _ _ _ p (square g x y Z z T θ U h u k b p v) _] -- tune order
lemma ticket_move (p:Space s)(v:Shade g Z (location Y i b,p) (2+U.horizon'))(n:TAxis): Face.Follow z (x.rent S z T θ U i b p) (x.rent S z T θ U i b (p+tstep n)) (inlet (Y.u i) Y.long (issue x z T θ U) b (p,n))=Face.Follow z (y.rent S z T θ U i b p) (y.rent S z T θ U i b (p+tstep n)) (inlet (Y.u i) Y.long (issue y z T θ U) b (p,n)):=by
 rw [signs g S x y Z z T θ U h u k b p (fun i p=> v i ((Gauss.base Y).mono (by omega) p)), signs g S x y Z z T θ U h u k b _ (shade_rides g Z _ (slide_n b p n)),face_eq g x y Z z T θ U h u k b p n (fun i p=>v i ((Gauss.base Y).mono (by omega) p))]; exact Nat.add_assoc 1 1 _ ▸ v -- syntax
end YM.CF.BProof.Mapping.Pawn
