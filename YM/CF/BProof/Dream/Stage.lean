import YM.CF.BProof.Dream.Bows
import YM.CF.BProof.Single.Realm
/-! Common gauge path and choice X for gap colors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Function Metric Extension.Mar Mag
open Cube Tenant Branch Fock Dial SU Tulip Lat Spin
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Kronecker
attribute [local instance] opCStarAlgebra
-- use γ argument at eased pace

def threes (M:Op Sheet): Stamp:= (1:Op (Fin 3))⊗ₖ M
lemma threesK {A:Op Sheet}(h:Aᵀ=A)(e:inK A):SealH (threes A):=by
 refine ⟨Matrix.kronecker_mem_unitary (unitary _).one_mem e.1,?_,?_⟩; unfold threes; rw [← Matrix.kroneckerMap_transpose,h,Matrix.transpose_one]; unfold threes; rw [Matrix.det_kronecker,e.2,Matrix.det_one]; simp
lemma threes_sub(X Y:Op Sheet): threes X-threes Y= threes (X-Y):=(op_kron_sub ..).symm
def comLin : Op Sheet→ₗ[ℂ] Stamp where
 toFun:=threes
 map_add' _ _:= by ext ⟨x,i⟩ ⟨y,j⟩; simp [threes,mul_add]
 map_smul' x y:= op_kron_smul ..
lemma threes_s : ContDiff ℝ ∞ threes:= (comLin.toContinuousLinearMap.restrictScalars ℝ).contDiff
lemma threes_motion (g:E)(B:Op Sheet): threes (mold (species g) B)=motion g (threes B):=by
 unfold motion congrC threes; simp only [SU.matter_matrix,SU.triple,mold,← Matrix.kroneckerMap_transpose, Matrix.transpose_one, op_kron_mul,mul_one,species]
lemma threes_inj:Injective threes:=by intro A B h; ext i j; simpa [threes] using Matrix.ext_iff.mpr h ((0:Fin 3),i) ((0:Fin 3),j)
def BB: Stamp:= threes living
def BBz(i:Fin 5):= threes (nodeB i)
lemma BBz_eq(i:Fin 5): BBz i=motion (locus i) BB:= threes_motion ..
@[simp] lemma BBz_zero :BBz 0= BB:=by simp [BBz,BB]
lemma BBz_diff {i:Fin 5}(h:i≠0): BBz i≠ BB:=fun p=> colour_n i h (threes_inj p)

def Gig (i:Fin 5)(t:ℝ): Stamp:= threes ((gamma i).seat t)
lemma sealG(i:Fin 5)(t:ℝ): SealH (Gig i t):= threesK ((gamma i).sound t).1 ((gamma i).sound t).2
lemma Gig_s (i:Fin 5): ContDiff ℝ ∞ (Gig i):= threes_s.comp (gamma i).seat_s
@[simp] lemma Gig_0 (i:Fin 5): Gig i 0=BB:=by simp [Gig,BB]
@[simp] lemma Gig_1 (i:Fin 5): Gig i 1=BBz i:=by simp [Gig,BBz,Gamma.seat1]
lemma Gig_z (t:ℝ): Gig 0 t=BB:=by simp [Gig,BB,(gamma 0).stays]
def tightLoop(M:Fin 5→Stamp)(r:ℝ)(i:Fin 5):Prop:=∀ x∈Zone, ‖Gig i x-M i‖≤r
lemma radC : ∃ (M:Fin 5→Stamp)(r:ℝ),0<r ∧ r<1∧∀ i,tightLoop M r i := by -- tune define below
 choose X r h R v using fun i=>(gamma i).rad; obtain ⟨i,hi,V⟩:= Finset.exists_max_image Finset.univ r Finset.univ_nonempty; refine ⟨threes ∘ X,r i,h i,R i,fun i t ht=>?_⟩; show ‖threes _-threes _‖≤_; rw [threes_sub]; exact (replicas_bound _).trans ((v i t ht).trans (V i (Finset.mem_univ _)))
-- dictionary orientation g (from e0)

def wing (i:Fin 5):= (scene i).wind
def XG(i:Fin 5)(s:ℝ): Ballot:= scaledV (wing i s) apex
def TG(i:Fin 5)(s t:ℝ): Stamp:= threes ((scene i).brace s t)
lemma TG_s (i:Fin 5): ContDiff ℝ ∞ (Function.uncurry (TG i)):=threes_s.comp (scene i).brace_s
lemma TG_seal(i:Fin 5)(s t:ℝ):SealH (TG i s t):= threesK ((scene i).checkpointU ..).1 ((scene i).checkpointU ..).2
lemma XG_s(i:Fin 5): ContDiff ℝ ∞ (fun s=> (XG i s).val):=by
 let L: Op F→ₗ[ℂ] Vect:= (ContinuousLinearMap.apply ℂ (Ket F) apex.val).toLinearMap.comp (Matrix.toEuclideanCLM (n:=F) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap -- tune arguments
 exact (L.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (scene i).wind_s
lemma XG0(i:Fin 5): XG i 0=apex:=by apply Subtype.ext; rw [XG,wing,(scene i).wind0]; exact act_one ..
lemma XG1(i:Fin 5): XG i 1= scaledV (locus i) apex:=by rw [XG,wing,(scene i).wind1]
lemma Xgz(s:ℝ): XG 0 s=apex:=by apply Subtype.ext; rw [XG,wing,(scene 0).windZ]; exact act_one ..
lemma compass(g:E)(B:Vect): motion g (Pair.fullM B)= Pair.fullM (turn g B):= (Pair.full_cong g B).symm
lemma TG_first (i:Fin 5)(s:ℝ): TG i s 0= Pair.fullM (XG i s).val:=by
 rw [TG,(scene i).beginT (by norm_num), threes_motion]; exact compass (wing i s) apex.val
lemma TG_flat (i:Fin 5)(s:ℝ): TG i s 1= BB:=by rw [TG,(scene i).bT _ _ (by norm_num) (by norm_num)]; rfl
lemma TG_Gig (i:Fin 5)(s:ℝ){t:ℝ}(h:1≤t): TG i s t=Gig i (ease s* tertiary t):=by unfold TG Gig; rw [(scene i).later _ _ h]
lemma TG_gig (i:Fin 5)(s:ℝ){t:ℝ}(h:1≤t): ∃ u∈ Zone, TG i s t= Gig i u:=by obtain ⟨ha,hb⟩:= easeZ s; have hi:tertiary t∈Zone:= easeZ _; exact ⟨_,⟨mul_nonneg ha hi.1,mul_le_one₀ hb hi.1 hi.2⟩, TG_Gig i _ h⟩ -- tune
-- simple dictionary for Mark collar (with deep ramp as u)
def BM (u t:ℝ): Stamp:= threes (shiftB (u*alpha t))
@[simp] lemma BM_x(u:ℝ):BM u 0=Pair.fullM apex.val:=by rw [BM,alpha0,mul_zero, shiftB_0]; rfl
lemma BM_0(t:ℝ):BM 0 t=Pair.fullM apex.val:=by rw [BM,zero_mul,shiftB_0]; rfl
lemma BM_fin(u:ℝ){t:ℝ}(h:3/8≤t): BM u t=threes (shiftB u):=by rw [BM,alpha_up h,mul_one]
lemma BM_1{t:ℝ}(h:3/8≤t): BM 1 t=BB:=BM_fin _ h
lemma BM_s : ContDiff ℝ ∞ (Function.uncurry BM):= threes_s.comp (shiftB_S.comp (contDiff_fst.mul (alphaS.comp contDiff_snd)))
lemma BM_seal(u t:ℝ): SealH (BM u t):= threesK (shiftB_T _) (KingB _)
lemma TG_d(i:Fin 5)(v:ℝ): TG i 0 v=BM 1 v:=by rw [TG,(scene i).brace_d, BM,one_mul]
lemma TG_z(s v:ℝ): TG 0 s v= BM 1 v:=by rw [TG,(scene 0).braceZ, BM,one_mul] -- not stationarity assertions for numeric refs?
lemma TG_tall (i:Fin 5){t:ℝ}(h:7/4≤t): TG i 1 t=BBz i:=by rw [TG_Gig _ _ (by linarith),ease_one,ter_up h,one_mul,Gig_1]
end YM.CF.BProof.Dream
