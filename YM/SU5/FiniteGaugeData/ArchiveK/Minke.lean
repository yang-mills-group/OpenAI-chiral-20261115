import YM.SU5.FiniteGaugeData.ArchiveK.Weld
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
namespace Midway
open Violas Waltz
variable {S T:Finset Cover}(A B:Finset Cover){F:Tulip.Male}{N:Side}{σ c C δ y k r a:ℝ}{n m d j:ℕ}
local notation "Ψ"=>inp N T
local notation "U"=>Beam B
local notation "Φ"=>flatH F N
abbrev stake(K:ℝ)(pB pT n:ℕ)(v:ℝ):ℝ:= pT*(n:ℝ)*(4*pB*K*v)
abbrev feeKX(pB:ℕ)(c C r:ℝ)(d j:ℕ):ℝ:= 4*pB*Real.exp (-c*d)*pride C+(C*4*pB*rover)*r^j
abbrev inertial (K r c C:ℝ)(pB pT n d j:ℕ)(v:ℝ):ℝ:=Real.exp (-c*d)*C*stake K pB pT n v+(pT:ℝ)*n*(feeKX pB c C r d j*v)
variable (M:Ruler (Beam B) (Fin n))(p:A⊆ S)(u:B⊆ S)(h:S⊆T)(H: Waltz N T)(g:∀ v'∈ S,∀ i∈ box d,v'-i∈T)
variable (b:0< c)(hr:0<r)(zr:r≤1)(B0:∀ x:Cover, x∉S→∀ v∈B,River r (emitX x) (emitX v))
local notation "Z"=> bar 4 F.val
local notation "Q"=> cutM (specW T B plusHalfᶜ)
local notation "G"=> fleece B M
local notation "Λ"=> inp N T*wall (T:=T) B M S
local notation "Υ"=> page U
local notation "Τ"=> page (Beam T)
variable (K:ℝ)(w:∀ x:Cover, ‖fpS x‖≤K) (kw:0≤ K)
include u p h H g b hr zr B0 K w kw
lemma engage (ℓ:Ream Z c C)(v: (Pick A B*M)ᴴ*(Pick A B*M)=1)(k0: tubeman B j*M=0)(om: ‖M‖≤ δ)(t:∀ x∈T,∀ v∈B, ‖∑ i∈Lattice.box d, tub Z i*fpS ((x-v)+i)‖≤Real.exp (-c*d)*pride C) : Suite n N F S A B (stake K Υ Τ n δ) (stake K Υ Τ n δ) (inertial K r c C Υ Τ n d j δ):=by
 let L:= Λ; let s₁:=cutM (WalU N A); let L1:=s₁*L; let s₂:= cutM (scel N); let L2:=s₂*L; let E:=stake K Υ Τ n δ; let e:= inertial K r c C Υ Τ n d j δ; let D:= plateH Z N d; obtain ⟨hp,hq⟩:= wall_abs A B M p h H v; let hU:= wall_back B M u h H; let hH:=grip_pay _ H.theta_t; have hx:0≤δ:= le_trans (norm_nonneg _) om
 have hW:{Y: Ruler (Beam T) (Fin n)}→ ‖inp N T*Y‖ ≤ ‖Y‖:=fun {Y}=> (Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_left (norm_nonneg Y) hH); have h1: ‖L‖ ≤ stake K Υ Τ n δ:= by
    apply le_trans hW; let Sx:= (4:ℝ)*Υ*K*δ; have hk:0≤Sx:=by unfold Sx; positivity; -- tune
    have hh(i:Cover): ‖(G) i‖ ≤ Sx:= (bust B M K w kw i).trans (mul_le_mul_of_nonneg_left om (show 0≤ 4 * (page U:ℝ)* K from by positivity)); let x:=torso_bill (T:=T) (reset S G) hk (fun i _=>by unfold reset; split; exact hh i; simpa); unfold wall; apply x.trans; simp [page,Sx,stake]
 refine ⟨L1,L2,L, ?_,wall_house B M h H⟩; refine ⟨by unfold L1; rw [←Matrix.mul_assoc, show _*s₁=_ from (cutM_idp _).1], hU, hp, hq,rfl, cutBudL.trans h1,h1,?_⟩
 let Y:=reset S G; let k:= tulp Y Z d; have he:D* L=inp N T*torso T k:= boot Y H h g (fun _ z=>if_neg z); let C₁:= feeKX Υ c C r d j; have hv:0≤C₁:=by obtain hl:=C_free ℓ b; have hz:=rover_n; have hv:=pride_p _ hl; unfold C₁ feeKX; positivity
 have hc : ‖D*L‖≤ (Τ:ℝ)*n*(C₁*δ):= by rw [he]; apply le_trans hW; apply le_trans (torso_bill k (mul_nonneg hv hx) (fun i hh=> (clip B M ℓ b t j u hr zr k0 B0 i hh).trans (mul_le_mul_of_nonneg_left om hv))); simp [page]
 have hm:‖(Φ - D)*L‖≤ Real.exp (-c*d)*C*E:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul (Ream.tollT N ℓ b.le d) h1 (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (C_free ℓ b))); rw [show Φ * L= (Φ - D)*L+D*L from ?_]; exact (norm_add_le ..).trans (add_le_add hm hc); rw [Matrix.sub_mul,sub_add_cancel]
-- all in terms of Montana parameters. choose K.E eventually 
omit H in
lemma messageR (u':∀ M:Tulip.Male,Ream (bar 4 M.val) c C)(y:0<δ)(Tκ:page (Invoice j)+n≤m)(t: found (Pick A B) m δ⁻¹) : ∃ V:ℕ,∀ F:Tulip.Male,V≤ F.val.val→∀ N:Side, Waltz N T→ Suite n N F S A B (stake K (page U) (page (Beam T)) n δ) (stake K (page U) (page (Beam T)) n δ) (inertial K r c C (page U) (page (Beam T)) n d j δ):=by
 obtain ⟨V,S',ΖΑ⟩:=t; let f:=tubeman B j; let g0:= (ract f).toLinearMap; let U':= V ⊓ LinearMap.ker g0; have he:dim U' ≥ n:= by have hx:= book V (LinearMap.ker g0); have ht:= ker_size g0; unfold U'; omega
 obtain ⟨M,k,hc,t0⟩:= heave (Pick A B) (inv_pos.mpr y) (V:=U') (fun x h=>ΖΑ x h.1) n he
 let ΖΑ:= T.biUnion (fun x=> B.image fun v=> x-v); obtain ⟨w₀,hw⟩:=earnM b u' d ΖΑ; refine ⟨w₀,fun M' ht N H=> engage A B M p u h H g b hr zr B0 K w kw (u' M') hc ?_ (by rw [inv_inv] at k; exact k) (fun i x v z=> hw M' ht _ (mem_biUnion.mpr ⟨i,x,mem_image_of_mem _ z⟩))⟩;
 apply ract.injective; rw [map_zero ract]; ext1 x; rw [Largo.R_mul]; exact (t0 x).2
#print axioms engage
#print axioms messageR
end Midway
end YM.CF.Window.ArchiveK
