import YM.CF.BProof.Prime.Horizon

/- Shelter. collect charges in halo near every fault. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Prime
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
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
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
open Scope Moment Push.AbsoluteSums
local notation "μz"=> Z.μwage
variable (k ξ:ℕ) -- near depth, and size cutoff in F support
open Branch Tenant Air Veil
variable {α C:ℝ}{I:Type}[Fintype I](K:Core j a₁ b l r N)
variable (Q:Primer N I α C)
local notation "Ψ"=> Pouch Y P T θ
local notation "ψx"=>Z.world1 P K
local notation "ψ0"=>Z.world0 P K
variable (x' : Pod Y)
open Account
namespace Shelter
variable (Y) (r':ℕ)(X:Cores Y r')(p:r'≥200)
abbrev crown := Cabinet.halo Y (fault Y r' x X) hNear -- not D-s (?)
abbrev paid := Cabinet.sober Y r' X (fault Y r' x X)
abbrev Surround := nearL Y x
include p
lemma crown_put (b:House.Block Y.yard Y.c')(t:b∈ crown Y x r' X): b∈ plate Y r' X:= by
 obtain ⟨i,v,h⟩:= (Cabinet.halo_m ..).1 t; exact ray_plate Y ((Cabinet.halo_m ..).2 ⟨i,(mem_inter.mp v).2,h⟩) (by unfold hNear; omega)
lemma paid_prop (h:X∈ recital Y r' x): paid Y x r' X=X.val \ Surround Y x :=by
 ext i; simp only [paid,Cabinet.sober,Finset.mem_sdiff]; exact and_congr_right fun k=>(fault_near Y r' X h k (by unfold hNear; omega)).not
lemma crown_unique : Set.PairwiseDisjoint (↑(recital Y r' x)) (crown Y x r'):=fun i l j t v=> disjoint_left.mpr (fun k k' hv=> v (belongsCore Y r' i j l t (crown_put Y x r' i p k k') (crown_put Y x r' j p k hv)))
lemma crown_all : (recital Y r' x).biUnion (crown Y x r')=Surround Y x:=by
 ext i; rw [mem_biUnion]; constructor; rintro ⟨j,l,u⟩; exact nearer Y _ _ (inter_subset_left (s₂:=j.val)) le_rfl u; intro h; obtain ⟨b,v,t⟩:= (Cabinet.halo_m ..).1 h; obtain ⟨q,p,u⟩:= atOwn Y r' (enlargement Y x v); exact ⟨q,p,(Cabinet.halo_m ..).2 ⟨b,mem_inter.mpr ⟨v,u⟩,t⟩⟩
lemma ring_unique : Set.PairwiseDisjoint (↑(recital Y r' x)) (paid Y x r'):=by
 intro i l j t v; change Disjoint (paid Y x r' i) (paid Y x r' j); rw [paid_prop Y x r' i p l, paid_prop Y x r' j p t]; exact disjoint_left.mpr (fun b k e=> v (belongsCore Y r' i j l t ((plan wB r').sub i (mem_sdiff.mp k).1) ((plan wB r').sub j (mem_sdiff.mp e).1))) -- tune rewrite pairwise fn
lemma paid_all:(recital Y r' x).biUnion (paid Y x r')=bitL Y x \ Surround Y x:=by
 ext i; rw [mem_biUnion]; constructor; rintro ⟨q,l,g⟩; rw [paid_prop Y x r' q p l] at g; exact mem_sdiff.mpr ⟨excited Y r' q l (mem_sdiff.mp g).1,(mem_sdiff.mp g).2⟩; intro h; obtain ⟨q,k,d⟩:= atOwn Y r' (mem_sdiff.mp h).1; exact ⟨_,k,paid_prop Y x r' q p k ▸ mem_sdiff.mpr ⟨d,(mem_sdiff.mp h).2⟩⟩ -- ▸
lemma approved (u:X ∈ recital Y r' x){i:House.Block Y.yard Y.c'}(v'i:i∈ crown Y x r' X) : ray mH i 32 ⊆ plate Y r' X:=funds_ray Y hNear 32 X (nearer Y _ _ (inter_subset_right (s₁:=sick Y x)) le_rfl v'i) (by unfold hNear; omega)
-- general rights. Measurable & Q readability.
omit p
section
structure Pitch where -- tune binder r'
   locations(Q:Cores Y r')(x:Pod Y):Finset (House.Block Y.yard Y.c')
   polar(Q:Cores Y r'):Measurable (locations Q)
   visible(Q:Cores Y r')(x y:Pod Y)(t:Spiced Y (plate Y r' Q) x y): locations Q x=locations Q y
-- Booth. support membership local; read values only there, giving meas and Phase.
variable {Y r'} (q:Pitch Y r')(F:House.Block Y.yard Y.c'→ Pouch Y P T θ→ℂ) (V':Cores Y r'→Pod Y→ℝ)
structure Ticket : Prop where
 freq(b:House.Block Y.yard Y.c'): Measurable (F b)
 sees(X:Cores Y r')(x y:Pouch Y P T θ)(l:X∈recital Y r' x.val)(v:X∈recital Y r' y.val)(p:Spiced Y (plate Y r' X) x.val y.val)(b:House.Block Y.yard Y.c')(g:b∈ q.locations X x.val): F b x=F b y
end
variable {Y P r'}
variable {F':House.Block Y.yard Y.c'→ Pouch Y P T θ→ℂ} {q: Pitch Y r'} (t:Ticket (P:=P) q F')  -- tune
namespace Ticket
abbrev bill(X:Cores Y r')(x:Pouch Y P T θ):= ∑ b∈ q.locations X x.val, F' b x
include t
lemma bill_m : Measurable (bill (F':=F') (q:=q) X) :=by
 apply Trek.meal ((q.polar X).comp measurable_subtype_coe) (fun i (x:Pouch Y P T θ)=> ∑ j∈i, F' j x); exact fun i=>Finset.measurable_sum _ (fun b _=>t.freq b)
def versionT : Cabinet.Shift Y P T θ r':=by
 refine ⟨fun i=> Total Y P T θ (bill (q:=q) (F':=F') i),fun i=> Scope.Total_m Y P T θ _ (bill_m _ t), ?_⟩
 intro X x y v p e l a; unfold Scope.Total; rw [dif_pos e,dif_pos l]; exact sum_congr (q.visible X x y a) fun b g=> t.sees X ⟨x,e⟩ ⟨y,l⟩ v p a b ((q.visible X x y a).symm ▸ (show b∈q.locations X y from g))
@[simp] lemma version_pay (h:Cabinet.Ready P Y T θ x): t.versionT.F X x=bill (F':=F') (q:=q) X ⟨x,h⟩:=dif_pos h
lemma version_income (g:ℝ)(W:∀ (x:Pouch Y P T θ)(X:Cores Y r'), X∈recital Y r' x.val→ ∀ b∈ q.locations X x.val, (F' b x).re≤ g): t.versionT.Income (fun X x=> ((q.locations X x).card:ℝ)*g):=by
 intro x X p h; rw [version_pay x X t p,bill,Complex.re_sum]; exact (sum_le_sum (fun i v=> W ⟨x,p⟩ X h i v)).trans_eq (by rw [sum_const,nsmul_eq_mul]); -- tune order
lemma issues (V:Finset (House.Block Y.yard Y.c'))(l:V=(recital Y r' x).biUnion (fun i=>q.locations i x))(k:Set.PairwiseDisjoint (↑(recital Y r' x)) (fun i=>q.locations i x))(e:Cabinet.Ready P Y T θ x): t.versionT.amt x= ∑ i∈ V,F' i ⟨x,e⟩:=by rw [l,sum_biUnion k]; unfold Shift.amt; exact sum_congr rfl fun i _=> version_pay x i t e
end Ticket
section
variable (Y r')
def Near : Pitch Y r':=⟨fun i x=>crown Y x r' i,fun i=> (measurable_of_countable (f:=fun t:Finset B=>Cabinet.halo Y (t∩ i.val) hNear)).comp (sick_m Y),fun i x y p=> by unfold crown; rw [Cabinet.inter_p Y y r' i p]⟩ -- tune
-- ensure paid equals Cabinet.Mint.paid
lemma paysM(X:Cores Y r'): paid Y x r' X= Cabinet.Mint.paid Y r' X x:=rfl
def Far : Pitch Y r':=⟨fun i x=>paid Y x r' i, fun i=>(measurable_of_countable (f:=fun A:Finset B=> i.val \ A)).comp ((Near Y r').polar i), fun i x y p=> congrArg (i.val \ ·) ((Near Y r').visible i x y p)⟩
end
end Shelter
end YM.CF.BProof.Prime
