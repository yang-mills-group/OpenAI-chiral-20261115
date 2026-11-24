import YM.Corona.Fit
import YM.CF.Hype.Tram
import YM.CF.Fans.Moon
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Roots
open Function Finset Filter Metric MeasureTheory Lattice Lattice.Corona Wilson Precision Pressure RG
open Jet Fock Cube Lat Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
variable {n:Side}
-- enumeration of sample paths (Mark circle scripts pay steep mixed bond). R0 fixed root.
local notation "K"=> Site n
abbrev pearl(r:ℕ):ℕ:= (r+r+1)^4
lemma ball_v (r:ℕ)(x:Site n) : (Lattice.halo r {x}).card ≤ pearl r:= (Corona.halo_size ({x}:Support n) r).trans_eq (by simp [pearl])
private lemma inside_b {c x:Site n}{r:ℕ} (p:separation c x≤r) : x∈Lattice.halo r {c}:=halo_spec.mpr ⟨c,by simp,p⟩
-- sample array via start + increments
abbrev StepsN(n:Side)(k:ℕ):= Fin (k+1) → Site n
variable(k N s m B t H:ℕ)(c r:Site n)
local notation "Φ" i:max=> StepsN n i
abbrev route_X(n:Side)(k:ℕ)(R:StepsN n k): Site n × (Fin k → Site n):= (R 0,fun i => R i.succ - R i.castSucc)
lemma ry_inj : Injective (route_X n k):=by
 intro A C h; obtain ⟨a,b⟩ := Prod.mk.inj (show route_X n k A= _ from h); funext i; induction i using Fin.induction with
 | zero=> exact a
 | succ i p=>
    have h1:= congrFun b i; change A i.succ-A i.castSucc=C i.succ - C i.castSucc at h1; rw [p] at h1; exact sub_left_inj.mp h1
abbrev ΦRoad (k:ℕ)(s H:ℕ)(c:Site n): Finset (StepsN n k) := by
 classical exact univ.filter fun R=> separation c (R 0) ≤ H∧∀ i:Fin k,separation (R i.castSucc) (R i.succ)≤ s
-- use signature k before c
lemma mold_count : (ΦRoad k s H c).card ≤ pearl H * (pearl s)^k :=by
 let A:= ΦRoad k s H c; let B:=Lattice.halo H {c}; let C:= Lattice.halo s ({(0:K)}:Support n); let W:= Fintype.piFinset (fun _ : Fin k=> C); let X:=B ×ˢ W
 have he: A.image (route_X n k) ⊆ X:=by
    rintro i v; obtain ⟨y,t,rfl⟩:= mem_image.mp v; obtain ⟨r,h⟩:= (mem_filter.mp t).2; refine mem_product.mpr ⟨inside_b r,Fintype.mem_piFinset.mpr (fun i=> inside_b ?_)⟩ -- mul norm
    change separation 0 (y i.succ-y i.castSucc) ≤ s; rw [separation,show (0:K)-_= y i.castSucc - y i.succ from by abel]; exact h _
 have hp:= card_le_card he; unfold X at hp; rw [card_product,Finset.card_image_of_injective A (ry_inj k)] at hp
 have hv:W.card=C.card^k:=by unfold W; simp -- tune
 rw [hv] at hp; exact hp.trans (Nat.mul_le_mul (ball_v ..) (Nat.pow_le_pow_left (ball_v ..) _))
variable {J:Type}[LinearOrder J][Fintype J](σ:J→Site n)
abbrev reach_B(s B:ℕ)(σ:J→ Site n)(y:Site n):=univ.filter fun i:J=>separation y (σ i)≤ B+s
abbrev poke_F(σ:J→ Site n)(X:Support n)(I:Finset J):Prop:=∀ i∈I,σ i∈X
abbrev lamp_B(s B t:ℕ)(σ:J→ Site n):Prop :=∀ y:Site n,(reach_B s B σ y).card ≤ t
abbrev TrackV(s B:ℕ)(σ:J→Site n)(k:ℕ)(R:StepsN n k):Finset J:= univ.biUnion fun i=> reach_B s B σ (R i)
local notation "ηo"=> N / s
local notation "Yσ"=> lamp_B s B t σ
lemma trackSize (p:Yσ) (R:StepsN n k) : (TrackV s B σ k R).card≤ (k+1)*t:=by
 unfold TrackV; apply card_biUnion_le.trans; refine (sum_le_sum (g:=fun _=>t) (fun i _=>p (R i))).trans_eq ?_; simp
-- one-step cover including c. KV subdivision H estimates.j visits at most `N/s+1` `. ghost labels not distinct may repeat anchor. count contours M not all sequences`
variable {D X:Support n}
lemma bore_Q (g:0< s)(h:c∈X)(R:ℕ → Site n)(w:covers B X D)(hu:∀ i∈D,∃ k≤ N,R k=i)(hz:∀ k<N,separation (R k) (R (k+1))≤1) (vo:N+B≤ H)(yk:N/s≤k)(L:Finset J)(p:poke_F σ X L): ∃ R': StepsN n k, R'∈ ΦRoad k s H c ∧ L ∈ (TrackV s B σ k R').powerset:=by
 let d(i:ℕ):ℕ:= min (i*s) N; let A:StepsN n k:=fun i=> R (d i); refine ⟨A,mem_filter.mpr ⟨mem_univ _,?_,?_⟩,?_⟩
 · obtain ⟨x,h,v⟩:= halo_spec.mp (w.1 h); obtain ⟨b,u,t⟩:= hu _ h
   change separation c (R (d 0))≤ _; unfold d; rw [Nat.zero_mul,Nat.min_eq_left (Nat.zero_le _)]; refine ((separation_triangle c x _).trans ?_); have ht:separation x (R 0)≤ b-0:=by rw [←t,separation_comm]; exact path_span hz 0 b (Nat.zero_le _) u
   rw [separation_comm c x]; omega
 · intro i; let a:= d i; let b:= d (i.succ); have hx:a ≤ b:=min_le_min (Nat.mul_le_mul_right s (by rw [Fin.val_succ]; omega)) le_rfl -- nonlinear s* via simp!
   change separation (R (d i.val)) (R b) ≤ _; refine (path_span hz (d i.val) b hx (Nat.min_le_right ..)).trans ?_
   unfold d b d; rw [Fin.val_succ,Nat.add_mul,Nat.one_mul]; omega
 apply mem_powerset.mpr; intro i hi; obtain ⟨x,h,t⟩:=halo_spec.mp (w.1 (p i hi)); obtain ⟨l,v,r⟩:= hu _ h
 let j:= l/s; let i':Fin (k+1):=⟨j,Nat.lt_succ_iff.mpr ((Nat.div_le_div_right v).trans yk)⟩
 have hj:j*s≤ l:=Nat.div_mul_le_self ..; have he:d i'=j*s:= Nat.min_eq_left (hj.trans v); have hu: l - d i' ≤ s:=by
    rw [he]; have h:= Nat.mod_add_div l s; have ht:= Nat.mod_lt l g; unfold j; rw [Nat.mul_comm s] at h; omega
 refine mem_biUnion.mpr ⟨i',mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
 apply (separation_triangle _ x _).trans; change separation (R (d i'.val)) x+ _≤ _; have hx: separation (R (d i'.val)) x ≤ s:=by rw [←r]; exact (path_span hz _ _ (he.symm ▸ hj) v).trans hu
 omega
local notation "Mp"=> ((m*(4*B+2))/s)
noncomputable def Knot_B(s B m:ℕ)(σ:J→ Site n)(c:Site n):Finset (Finset J):= by
 classical exact univ.filter fun i: Finset J => ∃ X:Support n,c∈X∧poke_F σ X i ∧ coverNumber B X≤ m
lemma pulse (g:0 < s)(i:Finset J)(p:i∈Knot_B s B m σ c):∃ v∈ΦRoad ((m*(4*B+2))/s) s (m*(4*B+2)+B) c, i ∈ (TrackV s B σ Mp v).powerset:=by
 unfold Knot_B at p; obtain ⟨X,h,t,v⟩:= (mem_filter.mp p).2
 obtain ⟨D,hD,d⟩:= coverNumber_realized B X; obtain ⟨k,hk,R,u,w⟩:= ring_path _ (halo_ship _ hD.2)
 have hs:k≤ m*(4*B+2):=by
    rw [show B+B+1+(B+B+1)=4*B+2 from by omega] at hk; exact hk.trans (Nat.mul_le_mul_right _ (d ▸ v))
 exact bore_Q _ k s B _ c σ g h R hD w u (by omega) (Nat.div_le_div_right hs) i t -- order
lemma energy_E (g:0<s)(p:lamp_B s B t σ): (Knot_B s B m σ c).card ≤ pearl (m*(4*B+2)+B)*pearl s ^Mp*(2^((Mp+1)*t))∧∀ L∈Knot_B s B m σ c,L.card ≤ (Mp+1)*t:=by
 let A:= ΦRoad Mp s (m*(4*B+2)+B) c; let W(v):=TrackV s B σ Mp v; let Z:= A.biUnion fun v=>(W v).powerset; let C:= Knot_B s B m σ c
 have he: C ⊆ Z:= fun i p=> mem_biUnion.mpr (pulse s m B c σ g i p) -- exact shape
 refine ⟨(Finset.card_le_card he).trans (card_biUnion_le.trans ?_),fun L i=>?_ ⟩
 · let M:=2^((Mp+1)*t); refine (sum_le_sum (g:=fun _=>M) (fun v _=>?_)).trans ?_
   · rw [Finset.card_powerset]; exact Nat.pow_le_pow_right (by norm_num) (trackSize _ _ _ t σ p v)
   simp only [sum_const,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (mold_count _ _ _ c)
 obtain ⟨v,h,hi⟩:= mem_biUnion.mp (he i); exact (card_le_card (mem_powerset.mp hi)).trans (trackSize _ _ _ t σ p v)
end YM.CF.Roots
