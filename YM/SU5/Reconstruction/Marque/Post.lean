import YM.SU5.Reconstruction.Marque.Cabinet
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Metric Bornology BridgeClub Picket Anvil ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace BigOperators Topology Classical Pointwise
variable {H:Hilbert} {S : OS.Semigroup H clock} (G: Gallery H S)
local notation "U"=> Picket.trans S
local notation "τ"=> parcelUp S
local notation "C"=> G.footprint
local notation "K"=> G.hue
local notation "M"=> G.lobby
variable (Ω:H)(j:Axis) (p:j≠clock)
local notation "W"=> Wedge clock j
local notation "D"=> stroll clock j p
variable (X:Chair G.lobby Ω j)
local notation "Z"=> X.boost
-- vac-only obligations
namespace Gallery
variable {G Ω j p X}
variable (b: Authenticates G Ω j p X)
variable {A B:H.Op}
-- coverage by generator translations & finite torso, pure geometry
include b
lemma hike(t:ℝ)(x:E4): Z t*mover S x=mover S (D t x)* Z t:= by ext1 y; simp_rw [wander_mul,mover_at]; exact (b.motion t x y).symm
variable (u:Fragment G Ω) (t:ℝ) (h:G.Tilts Ω j X t)
include u h
lemma upon {V:Set E4} (z:IsOpen V)(i:G.Row)(e:A∈ K i)(x:E4)(c:D t '' strace x (C i) ⊆ V) : Fleet.Form (X.convex t) (τ x A) ∈ M V := by
 obtain ⟨a₀,p1,d,p2,v⟩:=ahead (D t) (strace x (C i)) V ((G.close_footprint i).image (show Continuous (fun v:E4=>v+x) by fun_prop)) z c
 obtain ⟨q,g,hx⟩:=purchase b h d p2
 let U1:= mover S x; let T':=Z t; let T:=T' *U1; have gT:Fleet T false:= (transport S x).times (X.convex t)
 let S':= G.sprites q (thickening a₀ (C i))
 have hp:Promotes T (Auditorium S') (M V):= by
    refine promotes_bic gT (sprite_star _ _ ) ?_ -- tune
    rintro _ ⟨i',y,B,w,s,v',rfl⟩
    let β:= (X.convex t).Form B; have he: β∈ M (ball 0 d):= hx _ B s v'
    let v₀:=D t (x+y); have hy: x+y∈ thickening a₀ (strace x (C i)):= by
        obtain ⟨z,h,d⟩:=Metric.mem_thickening_iff.mp w; exact Metric.mem_thickening_iff.mpr ⟨z+x, ⟨z,h,rfl⟩, by rw[add_comm]; simpa only [dist_add_right] using d⟩ -- `rw [add_comm]` picks
    have hk:τ v₀ β∈ M V:= G.mono (v _ hy) (G.traceAppointment (ball _ _) v₀ _ he _ (mover_parcel S _ _))
    have ht:Across T (τ y B) (τ v₀ β):= by
        have hu: U1 * mover S y=mover S (x+y):= by unfold U1; ext1 q; rw [wander_mul,mover_at,mover_at,mover_at]; exact DFunLike.congr_fun (trans_sum S x y).symm q -- ext1 dune
        have H':= ((X.convex t).arr B).functor (mover_parcel S v₀ β)
        rw [show mover S v₀ * Z t = T*mover S y from (by unfold T T'; rw [mul_assoc,hu]; exact (hike b t _).symm)] at H';
        simpa only [mul_assoc, mul_inv_cancel,mul_one] using! (mover_parcel S y B).inv.functor H'
    rw[(gT.arr _).unique ht]; exact hk
 exact hp _ (payFragment b u a₀ q p1 g i e) _ ((mover_parcel S x A).functor ((X.convex t).arr _))
variable (G X p)
-- deed, implication
abbrev PoleHonor : Prop:=∀ V:Set E4, IsOpen V→Promotes (X.boost t) (G.lobby V) (G.lobby (stroll clock j p t '' V))
-- stepPay & at least to test local add $Light WORLD.
omit u h b
variable {G X p t}
local notation "L" t:max=>PoleHonor G p X t -- tune order Ω j
include b u h
lemma tilt_bound : L t:= by
 intro V z; refine promotes_bic (X.convex t) (G.tiles_meet V) ?_; rintro _ ⟨i,q,A,e,w,rfl⟩; exact upon b u _ h ((D t).isOpenMap V z) i e q (Set.image_mono w)
omit u h b
lemma plus_increment {s:ℝ}(g:L t)(h:L s): L (t+s) := by
 intro V e; have ht:=g _ ((D s).isOpenMap V e); rw [X.rise, show D (t+s) '' V = D t '' (D s '' V) from (by rw[Set.image_image,show (D (t+s):E4→E4)=(fun x=>D t (D s x)) from funext (stroll_add clock j p t s)])]
 exact promotes_trans (h V e) ht (X.convex _)
lemma direct0 : L 0:= by
 intro V e; rw[show D 0 '' V=V from (by rw [show (D (0:ℝ): E4→ E4)= id from funext (stroll_zero clock j p), Set.image_id]), X.beginning]; exact fun x e y p => ((Conveys.first _) x y p).1 e
lemma many(n:ℕ)(g:L t): L ((n:ℝ)*t):= by
 induction n with
 | zero=> simpa only [Nat.cast_zero,zero_mul] using (show L 0 from direct0)
 | succ n v=> simpa only [Nat.cast_succ,add_mul,one_mul] using plus_increment v g
end Gallery
end YM.Marque.Flow
