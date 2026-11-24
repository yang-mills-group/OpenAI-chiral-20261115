import YM.SatinExist.Violet
import YM.SatinExist.SlicePath
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {P: Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(H:Real.exp 1≤P.x)(s i:ℕ)
namespace Xara
local notation "W"=> tent Y H
local notation "Γ"=> side Y i s
section transport
variable (x y:Cover)(A:GemUT)(a b:SU.F)
private def simmer (N:Side):Mark N:= fun _=> Fock.remove (basisC N x (dnSpin A.2.2.1) (Bun A.1 a))*create (basisC N y (upSpin A.2.2.2) (Bun A.2.1 b))
local notation "μ" T:max=> simmer x y A a b T
private lemma shipL {U V:Side}(k:U=V): ship k (simmer x y A a b U)=simmer x y A a b V:=by subst V;rfl
local notation "τ"=> distribute Y H s i
lemma dish (V:Fields (side Y i s)): distribute Y H s i (clone (tent Y H) x y A a b).val V=Fock.remove (basisC (side Y i s) x (dnSpin A.2.2.1) (Bun A.1 a))*create (basisC (side Y i s) y (upSpin A.2.2.2) (Bun A.2.1 b)):=congrFun (shipL x y A a b (terrain Y H _ s)) V
end transport
lemma inaccessible_up (i:SpinIdx)(h:i∈plusHalf): ∃ j:Fin 2,i=upSpin j :=by fin_cases i<;> first|exact ⟨0,rfl⟩|exact ⟨1,rfl⟩|exact absurd h (by decide)
lemma inaccessible_down (i:SpinIdx)(h:i∉plusHalf): ∃ j:Fin 2,i=dnSpin j :=by fin_cases i <;> first | exact ⟨0,rfl⟩|exact ⟨1,rfl⟩|exact absurd h (by decide)
section frames
local notation "I"=> Single Γ
local notation "F"=> FC I
variable (S T:Finset Cover)(E:Dome (tent Y H)→ₗ[ℂ]ℂ)(v:E∈ (Set.univ : Set _))(r:MatterWard (tent Y H) E)(t:Disjoint S T)
variable (U:FC (Single (side Y i s))→ₗ[ℂ]ℂ)(e:∀ f∈bay (tent Y H) (S∪T) true,PureMatter (tent Y H) f→∀ V,U (distribute Y H s i f.val V)=E f)
local notation "κ" p:max q:max=> Fock.remove (basisKet p)* Fock.create (basisKet q)
variable (h:ℝ)(u:0≤h)(k:∀ (x:Cover),nodeC x∈ S→∀ y:Cover,nodeC y∈ T→∀ A B:GemUT,‖E (sheen (tent Y H) x A * sheen _ y B)‖≤ h)
include t r u k e
local notation "𝒮" i:max =>(speciesSet Γ false)
local notation "s!" S:max=> modesIn Γ (Satin.region S Γ)
local notation "n!" i:max=> (Tset Γ)
lemma diagram (a b c d:Single (side Y i s)) (p:a∈(Tset Γ)ᶜ) (q:b∈n! 1) (p':c∈ (Tset Γ)ᶜ) (q':d∈ n! 1)(f:a∈𝒮 0)(l:b∈𝒮 0)(f':c∈𝒮 0)(l':d∈𝒮 0) (x:a∈s! S)(y:b∈s! S)(x':c∈s! T)(y':d∈s! T): ‖U ((κ a b)*(κ c d))‖ ≤ if a.1.1=b.1.1 ∧ c.1.1=d.1.1 then h else 0:=by
 let N:=side Y i s
 rcases a with ⟨⟨a,i₁⟩,s'⟩; rcases b with ⟨⟨b,i₂⟩,t'⟩; rcases c with ⟨⟨c,j₁⟩,s₀⟩; rcases d with ⟨⟨d,j₂⟩,t₀⟩
 obtain ⟨h₁,m₁,rfl⟩:= bun s' (mem_filter.mp f).2; obtain ⟨h₂,m₂,rfl⟩:= bun t' (mem_filter.mp l).2; obtain ⟨b₁,a₁,rfl⟩:= bun s₀ (mem_filter.mp f').2; obtain ⟨b₂,a₂,rfl⟩:= bun t₀ (mem_filter.mp l').2
 obtain ⟨α,rfl⟩:= inaccessible_down i₁ (fun h=> (mem_compl.mp p) ((Window.mem_Tset ..).2 h)); obtain ⟨β,rfl⟩:= inaccessible_up i₂ ((Window.mem_Tset ..).1 q); obtain ⟨χ,rfl⟩:=inaccessible_down j₁ (fun h=> (mem_compl.mp p') ((Window.mem_Tset ..).2 h)); obtain ⟨η,rfl⟩:= inaccessible_up j₂ ((Window.mem_Tset ..).1 q')
 have ht{S Z}(M:SpinIdx)(K:SU.Slot)(v: ((Z,M),K)∈ modesIn N (Satin.region S N)) : ∃ i:Cover,nodeC i ∈S ∧ wrap N i=Z := by obtain ⟨j,l,m⟩:= mem_image.mp ((modes_at ..).1 v); obtain ⟨x,a,b⟩:=Tower.wrap_nodes N Z j m; exact ⟨x,a ▸ l,b⟩ -- tune
 obtain ⟨a,pa,rfl⟩:= ht _ _ x; obtain ⟨b,pb,rfl⟩:= ht _ _ y; obtain ⟨c,hc,rfl⟩:= ht _ _ x'; obtain ⟨d,hd,rfl⟩:= ht _ _ y'
 let A:GemUT:=(h₁,h₂,α,β); let B:GemUT:=(b₁,b₂,χ,η)
 let P':= clone W a b A m₁ m₂; let Y':= clone W c d B a₁ a₂
 have hp := limits W S T a c A B r t pa hc m₁ m₂ a₁ a₂ b d pb hd h u (k a pa c hc A B)
 have he:= e (P'*Y') ((bay W (S∪T) true).mul_mem (bum_bay _ _ a b _ _ _ _ _ _ (mem_union_left _ pa) (mem_union_left _ pb)) (bum_bay _ _ c d _ _ _ _ _ _ (mem_union_right _ hc) (mem_union_right _ hd))) (matterPure_mul W (bum_mat W _ _ _ _ _ _ _ _) (bum_mat W _ _ _ _ _ _ _ _)) (1,1)
 change U (distribute Y H s i (P'.val * Y'.val) (1,1))=_ at he; rw [(distribute_arith Y H s i _ _ 0).2.1,Pi.mul_apply,dish,dish] at he -- unfolding
 rw [←he] at hp
 simp only [basisC,Fock.remove,map_smul,star_smul,Matrix.mul_smul,Matrix.smul_mul, norm_smul, norm_star, Lifted.winding,fee_norm, one_mul] at hp
 unfold Fock.remove; apply hp.trans ?_ ; split_ifs with he g he
 all_goals first | exact u|rfl|exact absurd (show wrap N a = wrap N b ∧ wrap N c=wrap N d from ⟨congrArg _ he.1,congrArg _ he.2⟩) g
#print axioms diagram
end frames
end Xara
end YM.CF.Buffered.Afterglow.Six
