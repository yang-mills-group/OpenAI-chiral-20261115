import YM.CF.Vp929.Law.Correspond
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mos Mesa Cube Lat WalkBound Guide March Filter MeasureTheory
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
namespace Palace
namespace Pal
variable (x:Pal) (C:Side) (K:ℕ→ℝ)
def board(A:Realms):ℕ→Realms
 | 0=> A
 | n+1=> x.action A (board A n) C (K n) n
variable {x} {K}{C}
variable {A D:Realms}{p:Edge Cover}{v:Rooms}{n i B:ℕ}{o:Cover}
theorem fitBoard(n B:ℕ): ∃ R:ℝ,1≤ R ∧ ∃ (K:ℕ→ℝ) (N:ℕ), ∀ C:Side,N≤C.val→∀ x,Ready C B x →∀ A,Pal.Guards C n R x A (x.board C K A n):=by
 induction n with
 | zero=> exact ⟨1,le_rfl,0,0,fun C p x h A=>⟨fun _ _ _ _ _ _=>rfl,fun _ _ u=> by omega⟩⟩
 | succ n ih=>
    obtain ⟨R,v,K,N,q⟩:=ih; obtain ⟨L,T,p,H⟩:= Mos.united B R (zero_le_one.trans v)
    let S:=Function.update K n L; refine ⟨max R (L+2), le_trans v (le_max_left ..),S,max N T,fun C e x h A=>?_⟩; obtain Q:= bpaid h (q C ((le_max_left ..).trans e) x h A) (H C ((le_max_right ..).trans e)) v p
    have eq(i)(p:i≤n): x.board C S A i=x.board C K A i:=by
       induction i with
       | zero => rfl
       | succ i ih=> rw [board,show S i=K i from update_of_ne (by omega) ..,ih (le_of_lt p), board]
    rw [board,eq n le_rfl,show S n=L from update_self ..]; exact Q
section Daily

structure Atem (r B:ℕ)(o:Cover)(x y:Pal):Prop where
 knows: Aware x.lots y.lots o r
 charts: Chart x.rank y.rank o B r
 seats:∀ v:Rooms,v.bounded B→ Range r o v.foot→ x.showFrame v=y.showFrame v
variable {y:Pal} (r:Ready C B x)(t:Ready C B y)
protected lemma Atem.mono{R V:ℕ}(h:Atem R B o x y)(p:V ≤R): Atem V B o x y:=⟨h.knows.mono p,fun x e t=>h.charts x e (t.mono p),fun x e v=>h.seats _ e (v.mono p)⟩
local notation "b"=> B*C.val
include r t
theorem BoardBound(K:ℕ→ℝ){p n:ℕ} (v:Atem (p+n*40*b) (B*C.val) o x y)(q:Agrees {u|Range (p+n*40*b) o u} A D) : Agrees {u|Range p o u} (x.board C K A n) (y.board C K D n):=by
 induction n generalizing p with
 | zero=> exact fun i k t=> q i (by simpa using k) (by simpa using t)
 | succ n ih=>
   let P:= p+(B*C.val); let p' : P+n*40*b≤ p+(n+1)*40*b:=by unfold P; simp only [Nat.add_mul,Nat.one_mul]; omega
   have Ain:Agrees {x|Range P o x} (x.board C K A n) (y.board C K D n):=by
      apply ih (p:=P) (v.mono p'); intro i t h; exact q i ((t:Range _ _ _).mono p') ((h:Range _ _ _).mono p')
   let F:= x.board C K A n; let G:=y.board C K D n
   intro i u w; obtain ⟨z,H⟩:= emerge r i; let Y:=batch x.rank x.lots; let T:=4-z.dim; have e:z∈ Y T:= H.1.1; have u':=shoulder r.roof _ e; have U₀:= spanFits.mp (place H.2); let f(h:Cover)(p:here h≤z):= Range.trans (u:Range _ _ _) (within u' U₀.1 p); have k:P≤p+(n+1)*40*b:=by omega;
   have fv:= f _ z.foot_in; have eq:x.showFrame z=y.showFrame z:= v.seats z u' (fv.mono k); have d:P+(T+1)*6*b≤p+(n+1)*40*b:=by
      have he:T+1≤5:=by unfold T; omega
      have hc:(T+1)*6*b≤ 5*6*b:=by gcongr;
      unfold P at *; simp only [Nat.add_mul,Nat.one_mul] at hc ⊢; omega
   let vv:= v.mono d; have hY:y.Pri i z:=⟨⟨((connects T _ r.roof t.roof vv.charts vv.knows).eq z fv).mp e,rfl⟩,H.2⟩
   change x.action A F _ _ n i=y.action D G _ _ n i
   by_cases hz:z.dim=n
   · rw [release r H hz,release t hY hz,eq]; unfold Pal.replace; have he: Agrees z.marks A D:= fun i e t=> q _ ((f _ e).mono k) ((f _ t).mono k); have hi:wellF z A C 1 ↔ wellF z D C 1:=⟨fun p=>well_room he p,fun p=>well_room (fun i u v=>(he i u v).symm) p⟩; by_cases w:wellF z A C 1; rw [if_pos w,if_pos (hi.mp w),he _ U₀.1 U₀.2]; rw [if_neg w,if_neg (mt hi.mpr w), rateLocal (K:=K n) (C:=C) _ G (show Agrees z.marks F G from fun i e t=> Ain _ (f _ e) (f _ t))]
   rw [release_fail _ (fun ⟨u',uK,uZ⟩=> hz (unites r H uK ▸ uZ)),release_fail _ (fun ⟨u',uK,uZ⟩=> hz (unites t hY uK ▸ uZ))]; exact Ain i ((u:Range _ _ _).mono (Nat.le_add_right ..)) ((w:Range _ _ _).mono (Nat.le_add_right ..))

omit t
lemma runs(K:ℕ→ℝ)(n:ℕ):Measurable (fun A:Realms => x.board C K A n):=by
 induction n with
 | zero=> exact measurable_id
 | succ n ih=>
    apply measurable_pi_lambda; intro i; obtain ⟨T,h⟩:= emerge r i; by_cases k:T.dim=n; swap; · have h'(A): x.board C K A (n+1) i=x.board C K A n i:=release_fail x (fun ⟨u,v,e⟩=> k (unites r h v ▸ e)); simp_rw [h']; exact (measurable_pi_apply i).comp ih
    change Measurable (fun A=> x.action A (x.board C K A n) C (K n) n i); simp_rw [release r h k]; unfold Pal.replace
    let H:= (pickProof (x.showFrame T) T (K n) C).comp ih; exact Measurable.ite (Guide.Gallery T) (measurable_pi_apply _) ((((measurable_pi_apply i.1).comp H).inv).mul ((measurable_pi_apply (i.1+Lattice.step i.2)).comp H))
include t
lemma turns_board(K:ℕ→ℝ)(s:March)(h:x.Twist y s (B*C.val))(n:ℕ) : x.board C K (s.turns A) n=s.turns (y.board C K A n):=by
 induction n with
 | zero=> rfl
 | succ n ih=> simp only [board]; rw [ih,Pal.clockwise s h r t]
end Daily
end Pal
end Palace
end YM.CF.VolumeCape
