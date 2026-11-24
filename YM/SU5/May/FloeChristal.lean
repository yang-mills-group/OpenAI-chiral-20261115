import YM.SU5.May.FloeProof
import YM.SU5.Reconstruction.Hygrometry.Sandy
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open YM.Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "I"=>Complex.I
abbrev tariff(s:Personality): ℂ:= ActMark.applause s.down
lemma tariff_norm(s:Personality):‖tariff s‖=1:=by cases h:s.down<;>simp [tariff,ActMark.applause,h]
lemma tariff_ne_zero(s:Personality):tariff s≠0:=norm_pos_iff.mp (zero_lt_one.trans_eq (tariff_norm _).symm)
-- HERMIT from any of these style Hermio bills in quadratic form
section
variable {α:Type*}[Fintype α][DecidableEq α]
local notation "T"=> α→ℂ
def sprite (P:Op α)(x y:α→ℂ):ℂ:=∑ i,∑ j, star (x i)* P i j*y j
lemma sprite_nonneg (p:Op α) (h:∀ x:α→ℂ,0≤ sprite p x x) : 0 ≤ p:=by
 rw [Matrix.le_iff,sub_zero]; apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,fun t=>?_⟩
 · let F:=sprite p; have hx(i:α)(v:T): F (Pi.single i 1) v= ∑ a,p i a*v a:=by unfold F sprite; rw [sum_eq_single i]; simp; intro b _ v; simp [Pi.single_apply,Ne.symm v,v]; simp
   have hy (i j:α) (a:ℂ): F (Pi.single i 1) (Pi.single j a)=p i j*a:=by rw [hx]; simp [Pi.single_apply,mul_ite]
   have he (a b:α)(r:ℂ):
       F (Pi.single a 1+r • Pi.single b 1) (Pi.single a 1+r • Pi.single b 1)= F (Pi.single a 1) (Pi.single a 1)+F (Pi.single a 1) (r • Pi.single b 1)+star r*(F (Pi.single b 1) (Pi.single a 1)+F (Pi.single b 1) (r• Pi.single b 1)):=by
         unfold F sprite; simp_rw [Pi.add_apply,Pi.smul_apply, smul_eq_mul,star_add,star_mul', add_mul,mul_add,mul_sum,sum_add_distrib,mul_assoc]
   ext i j; have hw (x:T):(F x x).im=0:= (Complex.le_def.mp (h x)).2.symm; have f:=hw (Pi.single i 1+ (1:ℂ) • Pi.single j 1); have g:=hw (Pi.single i 1+Complex.I • Pi.single j 1); simp_rw [he,← Pi.single_smul'] at f g -- name tune
   simp only [hy, one_smul,smul_eq_mul,mul_one] at f g; have hp(a:α):(p a a).im=0:=by simpa only [hy,mul_one] using hw (Pi.single a 1)
   change star (p j i)=p i j; apply Complex.ext <;> simp [Complex.mul_im,Complex.mul_re,hp] at * <;> linarith only [f,g]
 · simpa [sprite,Matrix.mulVec,dotProduct,mul_sum,mul_assoc] using h t
end
variable {α:Type*}[Fintype α] {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y:Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j)
variable {R:ℕ→ℝ} (N:ℕ→Side) (p: Yard (fun i=>CSide (N i) B) R) (q:BudgetPoint)
local notation "j"=> K.j
variable (P₁:Ramp)(X:α→ Personality)
local notation "S" => whisper P₁
local notation "S'" => land_tilt P₁
include A g h p q
private lemma single_stake (u:α→ Gaia)(z:∀ i,face_tilt P₁ (u i)) (W:α→ℂ) : 0≤∑ i,∑ k, star (W i)*(I*tariff (X i)*poster (land_tilt P₁ (u i)) (u k) ((whisper P₁).role (X i)) (X k))*W k:=by
 apply le_trans (Overlook.tilted A g h N p q true (fun i=> [i]) W X P₁ u z (fun i=>rfl)); refine le_of_eq (sum_congr rfl fun i t=>sum_congr rfl fun k t=>?_); simp only [ActMark.royalties, List.map_cons, List.map_nil, List.prod_cons,List.prod_nil,mul_one, Hygrometry.couple, PriceCliff.quantum,List.cons_append,List.nil_append, Sum.elim_inl, Sum.elim_inr, Packed, Hygrometry.duo, comp_apply]; unfold tariff; change I*_*_*_*_= _; ring
local notation "Γ" M:max=>Trace K.j M
omit A g h p q in
private lemma redisplay {β γ:Type*}[Fintype β][Fintype γ](f:α→ β→α→γ→ℂ) : ∑ i:α×β,∑ k:α×γ,f i.1 i.2 k.1 k.2=∑ i,∑ k:α,∑ l:β,∑ w:γ,f i l k w:=by simp_rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
lemma polar_refund {M:Side}(U:α→ Cover)(w: Odd M.val)(t:∀ i,Clear P₁ K.j (U i))(P':α→ℂ):0 ≤ ∑ i,∑ k, star (P' i)*(I*tariff (X i)*cake ((whisper P₁).role (X i)) (X k) K.j M ((whisper P₁).cell (U i)) (U k))*P' k:=by
 let F(i:α×Trace K.j M): Personality:= X i.1 -- tune
 let Z(i:α× Trace K.j M): Gaia:= nature M (U i.1) i.2
 let y:ℂ:= ↑(mite (Γ M)); let C':α × Trace K.j M →ℂ:=fun i=>y*P' i.1
 have he:= single_stake A g h N p q P₁ F Z (fun i=>defined_now P₁ (U i.1) w _ (t i.1)) C'
 let T (i:α)(l)(k:α)(v):= star (C' (i,l))* (I*tariff (F (i,l))*poster (S' (Z (i,l))) (Z (k,v)) ((whisper P₁).role (F (i,l))) (F (k,v)))*C' (k,v)
 rw [Fintype.sum_prod_type] at he; simp_rw [Fintype.sum_prod_type] at he; change 0≤∑ i:α,∑ l:Trace K.j M,∑ k:α,∑ v:Trace K.j M,T i l k v at he; apply le_trans he; apply le_of_eq
 refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun k _=>?_ ; rw [cake_squall _ _ P₁ _ _ w]; unfold expected; simp_rw [mul_sum,sum_mul]; refine sum_congr rfl fun l _=> sum_congr rfl fun v _=>?_ ; unfold T F C'; rw [star_mul', show star y=y from Complex.conj_ofReal _]; unfold y Z; ring
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.polar_refund
#print axioms YM.CF.May.Floe.sprite_nonneg
