import YM.CF.BProof.Seam.Transfer
/-! View permission. Short & long variants work with the same dues. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Seam
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
abbrev framesL := color P Y T θ (tool Y x)
@[fun_prop] lemma frames_m : Measurable (framesL Y P T θ):=(Pawn.rent_m ..).comp (Brick.Act.pawn_m ..) -- order name
section
local notation "ζ_"=>framesL Y P T θ
local notation "DBz"=> 2*Deep.D mH
variable (i:Y.yard.Index)
abbrev cashL (b:Seat N):= Angular.V (Y.yard.u i) Y.yard.long Y.hall (rawK x) (ζ_ x i) b
abbrev gownL(b:Seat N) := Angular.stage (Y.yard.u i) Y.yard.long (rawK x) (ζ_ x i) b
variable {i Y P T θ x} (x':Pod Y)(e:Cabinet.Ready P Y T θ x)(h:¬Y.yard.D i){t:ℕ}{b:Seat N}(q:b∈ Y.yard.band i)
include e h q
lemma glance : gownL Y P T θ x i b= ζ_ x i (Angular.flag (Y.yard.u i) (time b) Y.yard.long) (space b):=by
 let T':= rawK x -- tuned
 have ht:= (proceeds P Y T θ _ e).2.2.2.flat; have hx:= stage_identity (Y.yard.u i) Y.yard.long (rawK x) (Y.yard.long_lt.trans Y.yard.count_lt) (fun v p hv hh=> ht (Y.yard.trunk_b p h hv hh)) (show b∈ (↑(Y.yard.band i):Set (Seat N)) from q); unfold gownL; nth_rw 1 [stage_layers]; rw [hx,Pi.one_apply, mul_one]
lemma cocoon : cashL Y P T θ x i b=Pawn.sightP Y.hall (tool Y x) y T θ (parcelT P Y) i (Angular.flag (Y.yard.u i) (time b) Y.yard.long) (space b):=by
 unfold cashL; rw [← Y.yard.high_fit i _ (rawK x) (ζ_ x) (proceeds P Y T θ _ e).2.2.2.flat h q]; have hx(y:Bool): inlet (Y.yard.u i) Y.yard.long (rawK x) y = inlet (Y.yard.u i) Y.yard.long (Setup.F' P Y T θ (tool Y x)) y:= Y.yard.sweeps_eq i _ (Y.yard.mix_field ..) h y; unfold Yard.high sight; rw [hx]; rfl -- tune notation
omit e h q
variable (Y P T θ)
-- Frobenius notation independent. compare link fields by not expanded gauge.
structure Probe (Λ:Finset (House.Block Y.yard Y.c')) (μ:Support (More N)) : Prop where
 door (t:Seat N)(p:t∈μ): ray mH (πX t) 8⊆Λ
 lawn (x y:Pod Y)(p:Cabinet.Ready P Y T θ x)(u:Cabinet.Ready P Y T θ y)(t:Spiced Y Λ x y): Agrees (↑μ) (rawK x) (rawK y)
 deep (x y:Pod Y)(p:Cabinet.Ready P Y T θ x)(u:Cabinet.Ready P Y T θ y)(t:Spiced Y Λ x y)(i:Y.yard.Index)(b:Seat N)(g:¬Y.yard.D i)(q:b∈μ)(f:Deep.rise mH (2*Deep.D mH) i (time b)): cashL Y P T θ x i b=cashL Y P T θ y i b
-- actuate on all Ready & share
section
variable (μ:Support (More N))
lemma fundsDoor {k:ℕ} (Z:House.Queue mH g₀ Y.hall μ k 8) (i:Seat N)(p:i∈μ) : ray mH (πX i) 8⊆Z.Z:=by
 intro j u; apply Pawn.listed g₀ K_ μ Z p; exact Grid.collar_mem.mpr ⟨πX i,mem_singleton_self _,(Grid.dist_symm ..).trans_le ((House.ray_spec ..).1 u).1⟩
lemma paysLong {k:ℕ} (Z:House.Queue mH g₀ Y.hall μ k 8) : Probe Y P T θ Z.Z μ:=by
 let w:= (Cabinet.parcelT P Y).horizon'; have ht:1+(Cabinet.parcelT P Y).horizon'≤8*Y.g.count.val:=by rw [chrono P Y]; have :=(agenda P Y).coverage; omega
 constructor; exact fundsDoor Y μ Z
 · intro x l v t h; exact Pawn.transcript g₀ K_ (tool Y x) (tool Y l) μ y T θ (parcelT P Y) (room P Y) Z (Brick.Act.agrees mH g₀ h) ht (proceeds P Y T θ _ v).2.2.1 (proceeds P Y T θ _ t).2.2.1 -- room
 intro x z v t h i b k u q; have hh:b∈Y.yard.band i:=mem_strip.mpr q.1; rw [cocoon v k hh,cocoon t k hh]; exact (Pawn.deep_eyes g₀ K_ (tool Y x) (tool Y z) μ y T θ (parcelT P Y) (room P Y) Z (Brick.Act.agrees mH g₀ h) ht _ k _ u q (by simp)).1
-- short. shallow
lemma paidSong (j:Y.yard.Index) {k:ℕ} (w:k<Deep.D mH)(Λ:Finset (House.Block Y.yard Y.c'))(h:∀ i:Seat N,i∈μ→ Y.yard.Vic j k (time i))(q:∀ t∈μ, ray mH (πX t) 8⊆ Λ): Probe Y P T θ Λ μ:=by
 have ht:2*k+1<Y.yard.long:=by have := Deep.D_le mH; omega
 constructor; exact q
 · intro x z l v t i d a; apply prior_step Y P T θ x z l v i t ((ray_in mH 8 (by decide : 1 ≤ 8)).trans (q i.1 d)) k (by omega); rw [show gE i.1=j from Posts.vic _ _ _ ht (h _ d)]; exact h _ d
 intro x y l v t i b _ u f; exact False.elim (Deep.height mH (2*Deep.D mH) i k f (by omega) (by omega) (h _ u))
end
namespace Probe
variable {Y P T θ}
variable {Λ:Finset (House.Block Y.yard Y.c')}{μ:Support (More N)}
variable (Sμ:Probe Y P T θ Λ μ)(vT:Spiced Y Λ x x')
include Sμ
lemma home (g:b∈μ): πX b∈ Λ:= Sμ.door b g (ray_home ..)
lemma cut {u:Support (More N)}(h:u⊆ μ):Probe Y P T θ Λ u:= ⟨fun b p=> Sμ.door b (h p),fun x y v t p=> agrees_mono (Sμ.lawn x y v t p) (coe_subset.mpr h),fun x y l v t i b p u e=> Sμ.deep x y l v t i b p (h u) e⟩
variable (l:Cabinet.Ready P Y T θ x')
include h vT
-- day
lemma label(g:b∈ μ) : let a:=Angular.flag (Y.yard.u i) (time b) Y.yard.long; let t:= (Y.yard.location i a, space b); b∈ Y.yard.band i → ζ_ x i a (space b)= ζ_ x' i a (space b):=by
 dsimp only; intro p
 let k:=Trek.tag mH b; let t:= (parcelT P Y).horizon'
 apply Pawn.signs g₀ K_ _ _ Λ y T θ (parcelT P Y) (room P Y) (Brick.Act.agrees mH g₀ vT) h; apply House.ray_loan mH g₀ Λ 8; rw [chrono]; have := (agenda P Y).coverage; omega
 rw [← Trek.code_tag mH i b p,hiddenD]; exact Sμ.door b g
include e l q
lemma eye (t:b∈μ) : gownL Y P T θ x i b=gownL Y P T θ x' i b:=by rw [glance e h q,glance l h q]; exact label x' h Sμ vT t q -- tune let
end Probe
end
end YM.CF.BProof.Seam
