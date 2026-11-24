import YM.CF.Exa.Water
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset Bloch
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
open Tap Tenant Proa
variable (N:Side)(z:Op Slot)
private lemma none_l {x:Cover}(v:x∈ porchY N)(h:wrap N x=0): x=0:=by
 obtain ⟨⟨i,g⟩,e,rfl⟩:= mem_image.mp v; change wrap N (g.act (lift i))=0 at h; rw [←wrap_signed,wrap_lift (n:=N)] at h; have hp:g.act (0:Site N)=0:=by simp
 rw [show i=0 from g.act_injective (h.trans hp.symm)]; simp -- tune
private lemma wind_q {p:Site N}: Rush.wind p (0:Cover) =1:=by
 have hx:= infT p (0:Cover); simp only [map_zero,add_zero] at hx; have ht:=add_eq_left.mp hx; have hh: periods N (natural p)=0:= (nsmul_right_injective (M:=Cover) N.property.ne' (by simpa only [smul_zero])); simp only [Rush.wind,add_zero,hh,Rush.fee]; simp
lemma wave_o(v:Momentum): heroP (plankP N z) v= waveB z:=by
 let T:= plankP N z; let G:= jump (Equiv.refl (Site N)) fun _=>waveB z
 have hp : rentH T=G:= (love N).symm_apply_apply _
 have hg:0∈ porchY N:= mem_image.mpr ⟨(0,1),mem_univ _,by simp⟩
 have hx:portY (0:Site N)={0}:= Finset.ext fun y=> by rw [mem_singleton]; exact ⟨fun a=> none_l N (mem_filter.mp a).1 (mem_filter.mp a).2, fun w=> w.symm ▸ mem_filter.mpr ⟨hg,(wrap N).map_zero⟩⟩
 unfold heroP; rw [sum_eq_single_of_mem _ hg]; swap
 · intro i p h; apply smul_eq_zero.mpr; right; unfold loft Haro.tapH; rw [if_pos p]; have hp0:wrap N i≠0:=fun w=> h (none_l N p w)
   rw [show matPH (plankP N z) 0 (wrap N i)= 0 from ?_,smul_zero,smul_zero]; unfold matPH; rw [show rentH _=_ from hp]; ext; simp [tap,G,jump_apply, Ne.symm hp0]
 rw [loft,Haro.tapH, if_pos hg, wind_q, map_zero,one_smul,hx,card_singleton]; simp only [Nat.cast_one,inv_one,one_smul]
 · unfold matPH; rw [show rentH _=_ from hp]; ext; simp [G,tap, jump_apply]
lemma weights(X Y:Op (Single N))(v: Momentum):heroP (X-Y) v= heroP X v-heroP Y v:=by
 unfold heroP; rw [←sum_sub_distrib]; apply sum_congr rfl; intro i p; have hp:matPH (X-Y) 0 (wrap N i)= matPH X 0 (wrap N i)- matPH Y 0 (wrap N i):=by unfold matPH rentH; rw [map_sub]; rfl
 simp only [loft,p,Haro.tapH,hp,ite_true, smul_sub]
lemma crownZ(F:Op (Single N))(j:ℕ)(t:1≤j)(M:Male)(g:AxisP (heroP F))(h:z=zeus j M (heroP F)): NullW (potion j M (heroP (F-plankP N z))):=by rw [show heroP (F-plankP N z)=fun x=>heroP F x-waveB z from funext (fun i=>by rw [weights,wave_o]),h]; exact excise j t M (heroP F) g
open Pastry Hest
variable (T:Chin N→ Core N)(C:Chin N→ Core N)(U:Bkg (More N))(V:Core N)
local notation "A"=> (T (Tulip.profile U))
lemma basisH (p:IsStarProjection A)(g:TagG A (partV N T C V (-(plankP N z)) (profile U))): exp (dg (partV N T C V (-(plankP N z)) (profile U)))= (nursery A p).cook (exp (boat (-(plankP N z))+boat (finT N T C V (-(plankP N z)) (profile U)))):=by
 let X:= -(plankP N z); let B:=finT N T C V X (Tulip.profile U)
 rw [Poly.rising, map_add, birth, birth]; let S:=partV N T C V X (Tulip.profile U); let P:= A; change exp (dg S)= exp (dg _+dg _); let H:=Kennel.capT P X; have hp: TagG P H:=tag_g X p
 have hY:TagG P B:=by rw [show B=S-H from (by unfold S partV; change _=H+B-H; abel)]; exact (rentF P S H p g hp).1
 rw [show Kennel.capT P B=B from Laic.capQ hY,← dg_add]; rfl -- tune
end YM.CF.Exa
