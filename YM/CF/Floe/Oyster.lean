import YM.CF.Floe.Rain
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
open Jet Phase.Sample MeasureTheory
open scoped ContDiff
variable{K b c d r R A C e d₁ d₂ v:ℝ}
variable {m B N:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{n:ℕ}
variable(S: Stamp m B)(Y:E→ Pack m B)(I:Set E)(x:E)(h:Tagged e K n Y I)(u:IsOpen I)(hx:x∈I)(hp:1 ≤ K)
variable (t:FireK I (fun i=>rock m B (Y i).1) d₁ n)
variable (w:∀ (A:Set E)(V:IsOpen A)(p:Cue m), A⊆I→FireK A (fun i=>loft m B (Y i).1 (Y i).2 p) d₂ n)
variable (v:Hub m)(Q: sanctioned m B S v)(f:Post m B→ℂ)(p:Eck m B S r f)(T:Room B e)(g:0≤A)
abbrev Moist (e:ℝ)(n:ℕ)(A:ℝ)(U:E→Pack m B)(f:Tide m B→ℂ)(F:Cue m)(I:Set E):=∀ z:Cue m,∀ i∈I,(∀ᶠ x in 𝓝 i, ((U x,F),z)∈ checked m B e)→ Allows n (fun x=>f ((U x,F),z)) i A -- binders tune
local notation "R0"=> chairs m B S
include h u p T t w Q hx g
lemma merit_F (l:∀ i:Cue m,Moist e n A Y (inks m B f v) i I): Allows n (fun x=>coastal m B (inks m B f v) (Y x)) x (mercury (chairs m B S).card n d₁ (mercury (chairs m B S).card n d₂ A)):=by
 let X:=inks m B f v; have ht:= irradiates p T v; let y(w:E):=rock m B (Y w).1; let B₁:= R0; have hf : Down m B₁ := nested_ch _
 have hB(i:Cue m)(x:E)(w':x∈I)(p:fall (y x) i ≠0): ZeroF m B (Y x).1 i:=law_rich m B _ _ p
 have he(u v:Cue m)(x:E)(i:x∈I)(k:AgreeF B₁ u v)(p':fall (y x) u≠0)(q:fall (y x) v≠0) : trip m B X (Y x,u)=trip m B X (Y x,v):=by
    let S₁:=Y x; let L:=loft m B S₁.1 S₁.2; let q₁:=hB u x i p'; let q₂:= hB v x i q; let g':= (h x i).1
    apply (banks_like (s:=B₁) (L u) (L v) (fun z=>X ((S₁,u),z)) (fun z=>X ((S₁,v),z)) hf hf ?_ ?_ (ht.shadeC (S₁,u) ⟨g',q₁⟩) (ht.shadeC (S₁,v) ⟨g',q₂⟩))
    · intro z; exact prod_congr rfl fun i h=> bid_limit i (fun _ _ _=>rfl) (fun _ _=>rfl) (k.less (hf i h)) (fun _ _=>rfl)
    intro j w l' F G; exact light_local p T _ Q (x:=((S₁,u),j)) (y:=((S₁,v),w)) ⟨⟨g',q₁⟩,bid_ready _ _ _ g'.2 q₁ F⟩ ⟨⟨g',q₂⟩,bid_ready _ _ _ g'.2 q₂ G⟩ k l' (fun _ _=>rfl) (fun _ _ _ =>rfl)
 let C:= mercury B₁.card n d₂ A; have hz:= w I u (Classical.arbitrary _) (Set.Subset.refl I); have hC:0≤ C:=g.trans (bigger n _ g hz.pos)
 apply waitB t (fun x' t=> trip m B X (Y x',t)) B₁ (fun x w=>hf) _ hC _ _ x hx
 · intro p' z v' pv
   let S':= I∩{z:E| fall (y z) p'≠0}; have hz: z∈S':=⟨v',pv⟩; have hO:IsOpen S':=by
      rw [isOpen_iff_mem_nhds]; intro z p; refine inter_mem (u.mem_nhds p.1) ((fire_num t p.1 _ _).continuousAt.eventually_ne ?_); exact p.2
   have hv:= w S' hO p' Set.inter_subset_left; let L':=fun i=>loft m B (Y i).1 (Y i).2 p'; have hW(i:E)(x:i∈ S'): (Y i,p')∈roster m B e:=⟨(h i x.1).1,hB p' i x.1 x.2⟩
   have hh(k)(i:E)(z:i∈S')(p:fall (L' i) k≠0) : ((Y i,p'),k)∈checked m B e:=⟨hW i z,bid_ready _ _ _ (hW i z).1.2 (hW i z).2 p⟩
   refine waitB hv (fun i z=>X ((Y i,p'),z)) B₁ (fun _ _=>hf) (fun k i z t'=>?_ ) g (fun i z U v l r q=> ?_) (fun i v=>ht.shadeC (Y i,p') (hW i v)) z hz
   · refine l p' k i z.1 ?_; filter_upwards [hO.mem_nhds z, ((fire_num hv z _ _).continuousAt.eventually_ne t')] with i hw ht using hh k i hw ht
   exact light_local p T _ Q (hh U i z l) (hh v i z r) (fun _ _=>rfl) q (fun _ _=>rfl) (fun _ _ _=>rfl)
 · intro x h y u hv hu hy; exact he y u x h hy hv hu
 exact fun i v=> ht.flowerC _ (h i v).1
end YM.CF.Floe
