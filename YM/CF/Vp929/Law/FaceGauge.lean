import YM.CF.Vp929.Law.Axis
set_option autoImplicit false
set_option maxHeartbeats 720000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mesa Cube Lat
open scoped Topology Classical Matrix.Norms.Frobenius NNReal
abbrev Elm := Cover → SU.E
namespace WalkBound
variable {X:Rooms}{C:Side}{L K:ℝ}{B n:ℕ}{t:Elm}{x y:Cover}
def TinyStep(C:Side)(t:Elm)(v:Rooms)(K:ℝ):=∀ x i,here x≤v→here (x+step i) ≤ v → GDist (t x) (t (x+step i)) ≤ K/C.val
lemma tinyPrice (x : Cover)(l:TinyStep C t X K)(v:here x ≤ X)(u:here y ≤ X): GDist (t x) (t y) ≤ Tour.taxi x y*(K/C.val):=by
 by_cases p:x=y; subst y; simp [GDist,Tour.taxi]
 obtain ⟨z,p,e,f⟩:=Tour.route X v u p; rw [f]; push_cast; set T:ℝ:= K/(C.val:ℝ); have he: GDist (t x) (t z) ≤ T:=by obtain ⟨i,e|r⟩:=e; subst z; exact l x i v p; unfold GDist; rw [r,dist_comm]; exact l z i p (r ▸ v)
 have P:= tinyPrice z l p u
 exact (dist_triangle _ (SU.group.mat (t z)) _).trans ((add_le_add he P).trans_eq (show _=(↑(Tour.taxi z y)+1)*T from by unfold T; ring))
termination_by Tour.taxi x y
decreasing_by omega
-- boundary tax: path inside face, combine two faces.Mixed vertices arbitrary.
variable (h: X.bounded (B*C.val))(v:Wide C.val X)
local notation "b"=> (B:ℝ)
local notation "D"=> (C.val:ℝ)
local notation "κ"=> (GDist (t x) (t y))
local notation "w"=> dist (X.deck x) (X.deck y)
def Trail (X:Rooms)(C:Side)(t:Elm)(L:ℝ):Prop:=∀ y, y.facet X → TinyStep C t y L
lemma common_tip {i:Axis}{x:Cover}(e:here x≤ X)(p:(X i).tips (x i)): here x ≤ update X i (Wall.lone (x i)):=by intro j; by_cases t:j=i; subst j; rw [update_self]; rw [update_of_ne t]; exact e j
variable (a:Trail X C t L)
include h v a
lemma budget_deck(tX:(here x).boundary X)(tY:(here y).boundary X)(hp:0≤L): GDist (t x) (t y) ≤ (8*((B:ℝ)*L)+2*Real.sqrt (SU.group.repDim:ℝ)*B)*dist (X.deck x) (X.deck y):=by
 let k:=Real.sqrt (SU.group.repDim:ℝ); have hk:0≤k:=Real.sqrt_nonneg _; change _ ≤ (8*(b*L)+2*k*b)*w
 have HT:0<D:=by positivity
 have hz: Tour.taxi x y/(C.val:ℝ) ≤ 4*(w*b):=by
    unfold Tour.taxi; push_cast; apply (div_le_iff₀ HT).2; refine le_trans (Finset.sum_le_sum (N:=ℝ) (fun i _=> taxDeck h tX.1 tY.1 i)) ?_; norm_num [Axis]; ring_nf; exact le_rfl
 have H: Tour.taxi x y * (L/(C.val:ℝ)) ≤ 4*(w*b)*L:=by
    rw [show _*(L/(C.val:ℝ))=(Tour.taxi x y/(C.val:ℝ))*L from (by ring)]
    exact mul_le_mul_of_nonneg_right hz hp
 obtain ⟨i,p,u,Xp,e⟩:=bound_edge tX; obtain ⟨j,o,r,Yp,f⟩:=bound_edge tY; let hx: x i=u := congrArg Wall.a Xp; let hy:y j=r:=congrArg Wall.a Yp;
 let Y₀:=Function.update X i (Wall.lone u); let Y₁:= Function.update X j (Wall.lone r); have left':= a Y₀ ⟨i,intro_door.2 p,u,e,rfl⟩; have right':=a Y₁ ⟨j,intro_door.2 o,r,f,rfl⟩; have x0:here x ≤ Y₀:= (by unfold Y₀; rw [←hx]; exact common_tip tX.1 (hx ▸ e)); have x1:here y ≤ Y₁:= (by unfold Y₁; rw [←hy]; exact common_tip tY.1 (hy ▸ f))
 by_cases l:i=j
 · subst j; by_cases g:u=r; · have he:Y₀=Y₁:= congrArg (fun u=> update X i (Wall.lone u)) g; obtain p:=tinyPrice x left' x0 (he ▸ x1); refine p.trans ?_; have hu:0≤ w:=dist_nonneg; have hg:0≤ b:=(by positivity); nlinarith [mul_nonneg hg (mul_nonneg hu hp),mul_nonneg hk (mul_nonneg hg hu)]
   have eL:1≤w*b:=by
      have h1:= taxDeck h tX.1 tY.1 i; have h2:= v i (intro_door.2 p); have hz:C.val ≤ (x i-y i).natAbs:=by unfold Wall.tips at e f; omega
      nlinarith only [show (C.val:ℝ) ≤ (x i-y i).natAbs from Nat.cast_le.mpr hz,h1,HT]
   unfold GDist; rw [dist_eq_norm]; apply (norm_sub_le ..).trans; rw [Gauge.unitary_frob (SU.group.mat_mul_star _), Gauge.unitary_frob (SU.group.mat_mul_star _)]; change k+k ≤ _; nlinarith [mul_le_mul_of_nonneg_right eL hp,mul_le_mul_of_nonneg_right eL hk]
 let z:=update y i (x i); have tZ: here z ≤ X:=by
    intro j; by_cases p:j=i; subst j; rw [show here z i=here x i from congrArg Wall.lone (update_self ..)]; exact tX.1 i
    exact (show here z j=here y j from congrArg Wall.lone (update_of_ne p ..)) ▸ tY.1 j
 have hxZ:z i=u:=by simp [z,hx]
 have hyZ:z j=r:=by simp [z,Ne.symm l,hy]
 have v₂:here z≤ Y₀:= (by unfold Y₀; rw [←hxZ]; exact common_tip tZ (hxZ ▸ e)); have v₃:here z≤ Y₁:= (by unfold Y₁; rw [←hyZ]; exact common_tip tZ (hyZ ▸ f))
 have μ:=tinyPrice x left' x0 v₂; have η:=tinyPrice z right' v₃ x1; have δ(k:Axis):((x k - z k).natAbs ≤ (x k-y k).natAbs)∧ ((z k - y k).natAbs ≤ (x k-y k).natAbs):= by by_cases p:k=i <;> simp [z,p]
 let W0:ℝ:= Tour.taxi x y; have ν: (Tour.taxi x z:ℝ) ≤ W0:= Nat.cast_le.mpr (sum_le_sum (fun i v=>(δ i).1)); have θ: (Tour.taxi z y:ℝ) ≤ W0:= Nat.cast_le.mpr (sum_le_sum (fun i v=>(δ i).2))
 exact (dist_triangle _ (SU.group.mat (t z)) _).trans <| (add_le_add μ η).trans (by nlinarith [mul_nonneg hk (mul_nonneg (show 0≤ b from by positivity) (show 0≤ w from dist_nonneg)), (mul_le_mul_of_nonneg_right ν (div_nonneg hp HT.le)),(mul_le_mul_of_nonneg_right θ (div_nonneg hp HT.le))])
omit h v a
private lemma stretch(B n:ℕ)(L:ℝ)(t:0≤ L) : ∃ N:ℕ,∃ K:ℝ,0≤K ∧∀ C:Side,N ≤ C.val→∀ X:Rooms,X.dim=n→ n≤3→ X.bounded (B*C.val)→ Wide C.val X→∀ t:Elm, Trail X C t L→∃ u:Elm,TinyStep C u X K ∧ ∀ x,(here x).boundary X→t x=u x:=by
 by_cases e:n≤3; swap; · exact ⟨0,0,le_rfl,fun _ _ _ _ p=>(e p).elim⟩
 let v:ℝ≥0:=⟨8*((B:ℝ)*L)+2*Real.sqrt (SU.group.repDim:ℝ)*B,(by positivity)⟩
 obtain ⟨r,P,eK,F⟩:=Mesa.lav e v; obtain ⟨N,h⟩:= exists_nat_gt (2/r); refine ⟨N,2*(P:ℝ),by positivity,fun C p X t' vQ y ν τ hh=>?_⟩; subst n
 let R:Set Cover:={x|(here x).boundary X}; let S:= deck X '' R; have hx:S.Finite:=((finite X).subset (fun x v=> (v:boundary ..).1)).image (deck X)
 have H: ∀ z∈ Mesa.Peri (Board X.dim),∃ y∈S,dist z y ≤ r:=by
    intro z hz; obtain ⟨A,hA,hb⟩:= deckNet ν z hz; refine ⟨_,⟨A,hA,rfl⟩,hb.trans ?_⟩; apply (div_le_iff₀ (by positivity)).2; rw [div_lt_iff₀ eK] at h; exact h.le.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr p) eK.le).trans_eq (mul_comm ..))
 let f(z:Board X.dim):= if v:∃ x,(here x).boundary X∧ deck X x=z then τ v.choose else 1; have fA(x)(p:(here x).boundary X):f (deck X x)=τ x:=by
    unfold f; split; rename_i H; obtain ⟨p',q⟩:=H.choose_spec; exact congrArg τ (deckInj B y p'.1 p.1 q); exact False.elim (by grind)
 obtain ⟨q,v,hQ⟩:=F S (fun z h=> by rcases h with ⟨x,p,rfl⟩; exact sail_peri p) hx H f (LipschitzOnWith.of_dist_le_mul (by
    rintro _ ⟨x,p,rfl⟩ _ ⟨z,k,rfl⟩; rw [Function.comp_apply,Function.comp_apply,fA _ p,fA _ k]; exact budget_deck y ν hh p k t))
 refine ⟨q ∘ deck X,fun x i p g=>?_,fun x e=> (fA x e).symm.trans (hQ (show deck X x∈S from ⟨_,e,rfl⟩)).symm⟩
 apply (v.dist_le_mul _ (sail p) _ (sail g)).trans; exact (mul_le_mul_of_nonneg_left (adjacent (i:=i) ν (Rooms.spanT.1 (span_fixed x i))) P.coe_nonneg).trans_eq (by ring)
lemma strength_All(B:ℕ)(L:ℝ)(t:0≤ L) :∃ N:ℕ,∃ K:ℝ,0≤K∧∀ C:Side,N≤ C.val→∀ X:Rooms,X.dim≤3→ X.bounded (B*C.val)→ Wide C.val X→∀ t:Elm, Trail X C t L →∃ u:Elm,TinyStep C u X K∧∀ x,(here x).boundary X→ u x=t x:=by
 choose N K V H using fun i:Fin 4=>stretch B i.val L t; refine ⟨∑ i,N i,∑ i,K i,sum_nonneg (fun i _=> V i),fun C p X u α ξ t h=>?_⟩; let i:Fin 4:=⟨X.dim,by omega⟩; obtain ⟨q,e,g⟩:=H i C (le_trans (single_le_sum (f:=N) (fun i _=>Nat.zero_le _) (mem_univ i)) p) X rfl u α ξ t h
 exact ⟨q, fun x t i' p=> (e x t i' p).trans (div_le_div_of_nonneg_right (single_le_sum (fun i _=>V i) (mem_univ i)) (by positivity)),fun x p=>(g x p).symm⟩
end WalkBound
end YM.CF.VolumeCape
