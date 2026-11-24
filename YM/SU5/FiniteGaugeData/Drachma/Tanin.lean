import YM.CF.Cascade.Doric
import YM.CF.Cour.Rite
import YM.CF.Moire.Niche

/-! # at-field-1 chiral determinant income, exact block relation. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.CF.Parcel.Tanin
open Next.Free
open Function Filter NormedSpace Lattice Laurent Bloch Wilson Precision Tree Finset Matrix Exterior
open Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Cour Fir Ember Aroma Cascade
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B m A n:Side}{ho:Odd L.val}{j:ℕ}{e:ℝ}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}

abbrev galaZ (j:ℕ)(n:Side)(M: Male):ℝ:= OrbT (tickA n) (spar j M (1:Bkg (More n))) 0
def photo_ψ(j:ℕ)(n:Side)(M: Male):ℝ:= -galaZ j n M

lemma den_color (U:Aim n): U.den 1=0:=by rw [← Moire.bloom_P,profile_trivial]; exact Moire.bloom_zero U
lemma earthZ(I:Pride n): pigment I (1:Bkg (More n))=0:=by
 have he(i:Signed): Yg (incX i) (1:Bkg (More n))=1:=by rw [Ywin]; ext; simp [Lattice.pull,Step.read]
 unfold Pec.pigment lexn zinger Pec.tag; simp_rw [he,silt_0]; simp
variable (M:Male)
def ampleR(j:ℕ)(n:Side)(M:Male):=tickA n*spar j M (1:Bkg (More n))
abbrev scaleQ(n:Side)(j:ℕ)(M:Male):Cab Slot n:=(love n).symm (Zoom n (ampleR j n M))
lemma iceQ(N:Side)(j:ℕ)(t:1≤j)(M:Male):scaleQ N j M= subHub (fun i=> shell j M.val (mel i) • bins Slot)+(1-flatV Slot N):=by
 let A:=tickA N; let C:=spar j M (1:Bkg (More N)); let P:= (love N).symm; let U:= ampleR j N M
 have he: P U=subHub (fun i=>fuel Slot j M.val (mel i)):=by
    rw [show U=grace j M (0:Dress N) 0 from ?_]; exact base_grace t M (0:Dress N) rfl
    unfold U ampleR grace postR; simp [Crops,capT] -- tune
 unfold scaleQ Zoom; rw [map_add,map_mul,map_star,map_sub,map_one,plusInk,StarAlgEquiv.symm_apply_apply]; change P U*star (P U)+_= _; rw [he, subhub_star]; congr 1; rw [show subHub (N:=N) (fun i=>fuel Slot j M.val (mel i))* subHub (fun i=> star _) =_ from lung (Equiv.refl _) _ _]; congr 1; exact funext fun i=> fuel_p _ _ _ M.property _ (base_subset_realCube zone_pos (mel_h i))
lemma cold (N:Side)(j:ℕ)(t:1≤j)(M:Male): IsUnit (scaleQ N j M):=by
 rw [iceQ _ j t]; -- from Park
 let A:=flatV Slot N; let X:=subHub (fun i=>shell j M.val (mel (N:=N) i) • bins Slot); let Y:=subHub (fun i=> edgeH Slot j M.val (mel (N:=N) i)); let F:= subHub (fun _:Site N=> bins Slot); have he:A=F:=bin_hub.symm
 have hp(k:Site N):shell j M.val (mel k) ≠0:=div_ne_zero (fun h=> (noGhost (p:=mel k) (N:=M.val) (base_subset_realCube zone_pos (mel_h k)) (mel_away k)).ne' (congr_arg Complex.re h)) (mass_ne j _ M.property (base_subset_realCube zone_pos (mel_h k)))
 have hG (U V:Site N→Op (coneA Slot)): subHub U*subHub V=subHub (fun i=> U i*V i) := lung (Equiv.refl _) U V
 have h: (X+(1-A))*(Y+(1-A))=1:=by
   have ht:X*Y=A:=by unfold X Y; rw [hG]; simp_rw [edgeH,Matrix.mul_smul,Matrix.smul_mul,binsSq, inv_smul_smul₀ (hp _),he]; rfl
   have hu: X*A=X:=by unfold X; rw [he,hG]; simp_rw [Matrix.smul_mul,binsSq]
   have hv:A*Y=Y:=by unfold Y; rw [he,hG]; simp_rw [edgeH,Matrix.mul_smul,binsSq]
   rw [add_mul,mul_add,mul_add,ht,mul_sub,sub_mul (1:Cab Slot N) A Y,hu,hv,mul_one,one_mul,sub_self,sub_self,mul_sub,mul_one,sub_mul 1 A A,one_mul,show A*A=A from flatA.1]; abel
 exact Fock.live_of h
variable (G:Ratio (CSide m B) (CSide A B))(h:G.count=L)(k:P.roundZ ≤ (CSide m B).val) (p:0<e)(t:1≤j)
include h t
lemma v_zero (l:Even j) : fruit L j ho G M (1:nomA m A B) 0 =0:=by
 unfold fruit traitP Thera.creep; let x:nomA m A B:=1; have hy: unionP x=1:=by change (profile (1:Bkg _),profile (1:Bkg _))= _; simp [profile_trivial]
 rw [show unionP _= _ from hy]; simp only [bentT,mul_zero,add_zero,one_mul,mul_one,inv_one]; apply Thera.endorseI G; rw [spry]; change lum _ _ _ _ true M G 1=endorse G 0; rw [cologne j L ho l t (Thread j) (canUse _ _ ho) _ _ h,betP (0:Op (Iota G))] -- maybe t implicit include
include k t p
lemma relative_f (l: Even j)(U:Aim (CSide A B))(I:Pride (CSide A B))(K:Pride (CSide m B)): (shipA G P M U.den I K (1,1)).re=galaZ j (CSide A B) M-galaZ j (CSide m B) (upMale L ho M):=by
 let N:= CSide A B; let N':=CSide m B
 let q:Nom N' N:=1; let x:=spar j M (1:Bkg (More N)); have g:JointB G q e:= (near_j G e p).self_of_nhds; let α:Op (Single N):=0
 have he: foot G α=0:=rfl; have hp: desire L j ho G M q (foot G α)=0:=by rw [he]; unfold desire bentT; apply mul_zero
 have ht : trace (tickA N)=trace x:=(rank_z N t M).symm; have hf: IsUnit ((love _).symm (Zoom _ (tickA N*(1+α)*x))):=by rw [add_zero,mul_one]; exact cold N j t M
 have hD:‖desire L j ho G M q (foot G α)‖<1:=by rw [hp]; simp
 have hx:TagG x α:=⟨mul_zero _, zero_mul _⟩; have hw:= laser p G h k M q g hx hD ht (koh q g h k _ hD hf ht); rw [he] at hw hp; rw [hp, v_zero M G h t l] at hw; have he':coatG L ho j G M U.den q=0:=by unfold coatG Kennel.gate; rw [show U.den q.1=0 from den_color U, crux, capT,show foot G (0:Op (Single N))=0 from rfl,mul_zero,zero_mul]; exact hp
 unfold shipA; change (pigment I 1+(-(altar G P q M)-invoice (coatG L ho j G M U.den q))-pigment K 1).re= _; rw [earthZ,earthZ,zero_add,sub_zero,he',Complex.sub_re,Complex.neg_re]; rw [Complex.add_re] at hw; change galaZ j N M=_+galaZ j N' _ at hw; linarith -- tune
omit h k
-- Actual amount is always nonpositive. nonsing of one-period fiber via noGhost at half mesh. usable start estimate.
lemma heat_budget (k:P.roundZ ≤ (CSide m B).val) : photo_ψ j (CSide m B) M ≤ 0 ∧ inner ℂ (mateK (CSide m B)) (changeM (m:=m) P 1 M) ≠ 0:=by
 let n:= CSide m B; let A:=tickA n; let X:= spar j M (1:Bkg (More n)); have he:IsStarProjection X:= (P.broadness n k M).projection 1 (guard0 p.le); let v:= changeM (m:=m) P 1 M; let U:=mateK n; have hu: Sea A U:= tickB ..; have hv:Sea X v:=sea_g k _ (guard0 p.le) M; have ht:Matrix.trace A=Matrix.trace X:=(rank_z n t M).symm
 let Z:= inner ℂ U v; have hh:Real.log ‖Z‖=photo_ψ j n M:=by
    have hh:= orb_snap X A 0 v hv U hu he (plus_P _) ht -- tune hv
    rw [add_zero,skyGlow,quant_one,act_one] at hh; exact hh
 change _ ≤ 0 ∧ Z≠0
 constructor; · exact hh ▸ (Real.log_nonpos (norm_nonneg _) ((norm_inner_le_norm U v).trans (by rw [hu.2,hv.2]; simp)))
 intro hx; apply (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (cold n j t M))); rw [scaleQ]; change ((Zoom n _).submatrix _ _).det=0; rw [Matrix.det_submatrix_equiv_self]; unfold Zoom ampleR
 have H:=prismK he (plus_P _) ht 1 v hv U hu; rw [skyGlow,quant_one,act_one,show inner ℂ U v=0 from hx,norm_zero,zero_pow (by decide:(2:ℕ)≠0),Complex.ofReal_zero] at H -- tune hx'.
 dsimp only at H; rw [mul_one] at H
 exact H.symm
end YM.CF.Parcel.Tanin
