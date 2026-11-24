import YM.SU5.Registration.Heave.HaloLine
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open Lamour.Bridge CF.Pannier.Chancel
variable {Z θ b v t ε R C ξ:ℝ} {n a y z' k:ℕ}
universe u0
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
open YM.CF.Lamour.Bridge.Celeste
open YM.CF.Lamour.Bridge.Celeste.Morn
open YM.CF.Lamour.Bridge YM.CF.Velvet

namespace LaceLayer
open Yoke Tower Tower.SlabMark Tower.SlabMark.ClockBooking Sonnet
variable {r p d:ℕ}{σ:ℝ}

-- After optics & support/radius: per-site exponent. Notice dependence on w.
def costweight (K:Calibration)(r p w:ℕ):ℕ:=
  (4*(4*(r+p)+addgap K))^3 * (2*(16*K.B.val*(w+w)))
variable (B:0≤C) (U:Meringue.{0} Y p r (180*d) ε ξ C σ θ)
local notation "K"=> tent Y H
local notation "Λ!"=> ((4*(r+p):ℕ)+addgap K)
variable {w:ℕ}

include B U
lemma please_leaf (j:Axis)(T:Finset Cover)(f:Weaver)(g:0∈T)(gT:d=T.card)(e:r=breadth 0 T)
    (z:0<σ)(u:0<w)(Z:0<θ)(a₀: θ*(costweight (tent Y H) r p w:ℕ) ≤ 1)
    (h₀: ((↑(2*(r+p)+(p+1):ℕ)):ℤ) ≤ (Tower.SlabMark.ruler P.block)*(w:ℤ))
    (V:Voice f T)(X:∀ (N:Side)(x:Fields N),‖f N x‖≤C)
    (G:∀ (N:Side)(x:Fields N),Rightful (dBook N T) x.1 1 ξ → Rightful (dBook N T) x.2 1 ξ →‖f N x-f N (1,1)‖≤ ε)
    (R₁: Clarity f P.K.j (σ/4)) :
    ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,Ferry Y s i k → IcePlot Y s i k →
    ∀ n:ℕ,∀ v:ℤ, 0<n → 2*(ruler P.block*((w+w:ℕ):ℤ)*(n:ℤ)) ≤ (((side Y i s).val:ℕ):ℤ) → (((side Y i s).val:ℕ):ℤ) ≤ 4*(ruler P.block*((w+w:ℕ):ℤ)*(n:ℤ)) →
      ‖sharp Y H s i k (banner j ((w+w:ℕ):ℤ) (((w+w:ℕ):ℤ)*v) n (relocate (tent Y H) j (w:ℤ) (household (tent Y H) f)))‖ ≤ (3*(Real.exp 1*σ))^(4*n):=by
 let K':= tent Y H
 let F:= Real.exp 1*σ; have ht:0 < F:= mul_pos (Real.exp_pos 1) z
 let Q:= costweight (tent Y H) r p w
 let H!:Buffered.Family (tent Y H):= relocate (tent Y H) j (w:ℤ) (household (tent Y H) f)
 have he:ruler P.block*((w+w:ℕ):ℤ)=(↑(16*P.block.val*(w+w):ℕ):ℤ):=by unfold ruler; push_cast; rfl
 filter_upwards [U] with s v;
 have hp:Tendsto (fun i:ℕ=> ((count Y s i).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (count_grows Y s)
 filter_upwards [v,(count_grows Y s).eventually_ge_atTop Λ!, hp.eventually_ge_atTop (C*(16/F)), ((count_la Y s).eventually R₁), (count_la Y s).eventually (breadthMoney 0 T), (count_la Y s).eventually (ownsHalo (j:=P.K.j) (by rw [P.kJ]; decide))] with i x hs T0 r₀ q₁ h i' hF hP n z' hn H₁ H₂
 let N:= count Y s i; let E:=Journey.compass Y i i' s; let Z:= Journey.solder Y i i' hF.depth s; let M:= (gram Y s i i').J.M
 have gH:HaloTw P.K.j N:=h (Vale.val_e ..); let R:=4*n
 have hz: (Sonnet.Cost P.K.j r d M ε ξ C σ ⟨f N,dBook N T,wrap _ (0:Cover)⟩):= ⟨⟨X N,G N⟩,V.2 N,V.1.bounded N,gT.symm ▸ card_image_le, e.symm ▸ fun x h=> q₁ h, mem_image_of_mem _ g, r₀ (Vale.val_e ..) M⟩
 let W:= hull j r d p M ε ξ C σ gH
 obtain ⟨A,l⟩:= booth_lease Y H (j:=j) f 0 (map_zero _) T gH p hz h₀
 obtain ⟨L,t,t'⟩:= banner_from_unit Y H s i W (w+w) l n H₁ z'; rw [one_mul,one_mul] at t
 obtain ⟨g,gT⟩:= hut_fiber gH t.toStretch
 have hN:2 * (16*P.block.val*(w+w)) * n ≤ N.val:=by
    rw [he,←mul_assoc] at H₁; exact_mod_cast H₁
 have ha:N.val ≤ 4 * (16*P.block.val*(w+w)) * n:=by
    rw [he,←mul_assoc] at H₂; exact_mod_cast H₂
 let Λ':= 4*(r+p)+addgap K'; let S:= Finset.univ.erase j
 obtain ⟨k', ht', Y₁, V'⟩:= transversal_capacity (N:=N) (Nat.add_pos_right (4*(r+p)) addgap_pos) (show 0 < (16*P.block.val*(w+w)) from by positivity) hN ha hs
 let J:=(2^k')^3; have hJ:0<J:=pow_pos (pow_pos two_pos _) _
 obtain ⟨L',wV,hL,hL'⟩:= scatter gH (revive Y H s i i' hF) (terrain Y H _ s).symm (p₀:=p) ht' S L g (fun k v=> gT k (mem_erase.mp v).1)
 have ht: S.card=3:= by unfold S; rw [card_erase_of_mem (mem_univ _)]; simp [Axis]
 rw [ht] at hL hL'; have hL'':L'.length=J*R:= hL.trans (congrArg (J*·) t')
 change ‖E (Tower.distribute Y H s i (SlabMark.banner j _ _ n H!))‖ ≤ (3*F)^R; rw [show Tower.distribute _ _ _ _ _= _ from t.bill]; change ‖E (buffet L)‖ ≤ (3*F)^R
 have hg(List':List (Sonnet N))(w:Sylvan P.K.j r d p M ε ξ C σ List')(h:List'.length≤ (More N).val^4):‖E (buffet List')-Z (buffet List')‖≤ F^List'.length:= (hP _ (buffet List') (C^List'.length) w.occupy.env (buffet_price B w)).trans (hailW Y i (show 0 < F from mul_pos (Real.exp_pos _) z) B T0 h)
 have h₀:L'.length≤ (More N).val^4:= hL''.trans_le Y₁
 have hB': θ*sites N ≤ (L'.length:ℝ):=by
    have h:sites N ≤ (↑(L'.length*Q:ℕ):ℝ):=by unfold sites; rw [hL'']; exact_mod_cast V'
    have hg:= mul_le_mul_of_nonneg_left h (show 0≤θ from le_of_lt (by assumption)); have h':=(mul_le_mul_of_nonneg_left (show θ*(Q:ℝ) ≤ 1 from a₀) (show 0≤ (L'.length:ℝ) from Nat.cast_nonneg _)); push_cast at hg; linarith only [h',hg]
 have y₀: ‖E (buffet L')‖ ≤ F^L'.length:=by
    refine (broken_ratio Y i s i' (buffet L')).trans ?_; rw [striking L']; apply le_trans (x i' hF.depth hF.enters _ _ _ (Sonnet.S ∘ L'.get) (Sonnet.o ∘ L'.get) ?_ ?_)
    · unfold F; rw [mul_pow,←Real.exp_nat_mul,show σ^L'.length=Real.exp ((L'.length:ℝ)*Real.log σ) from by rw [Real.exp_nat_mul,Real.exp_log z], ←Real.exp_add,mul_one,Finset.card_univ,Fintype.card_fin]; exact Real.exp_le_exp_of_le (add_le_add hB' le_rfl)
    · intro i E'; exact (wV.core _ (List.get_mem ..)).issued gH.1
    · intro i e j p u; rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne u) with t|t; exact wV.annex.rel_get_of_lt (show i < j from t); exact Distant.symm (wV.annex.rel_get_of_lt (show j < i from t))
 have hY₁: ‖Z (buffet L')‖≤2*(F^L'.length):=(norm_le_norm_sub_add _ (E (buffet L'))).trans (by rw [norm_sub_rev,two_mul]; exact add_le_add (hg _ wV h₀) y₀)
 have hY: ‖Z (buffet L)‖ ≤ 2* (F^L.length):=by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hJ.ne').mp (hL'.trans (hY₁.trans ?_)); rw [mul_pow (2:ℝ) (F^L.length) J,←pow_mul F L.length J,hL]; change 2*F^(J*L.length) ≤ (2:ℝ)^J*F^(L.length*J); rw [mul_comm L.length J]; exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ (a:=(2:ℝ)) (by norm_num) hJ) (by positivity)
 have Lg:L.length ≤ (More N).val^4:= by rw [t']; exact le_trans (Nat.le_mul_of_pos_left _ hJ) Y₁; -- inference check
 refine (norm_le_norm_sub_add _ (Z (buffet L))).trans ((add_le_add (hg _ g Lg) hY).trans ?_); rw [mul_pow (3:ℝ) F R]; change _ ≤ (3:ℝ)^R * F^R; rw [show L.length=R from t']; have h: (3:ℝ) ≤3^R:=by simpa only [pow_one] using pow_le_pow_right₀ (a:=(3:ℝ)) (by norm_num) (show 1≤R by unfold R; omega)
 linarith only [mul_le_mul_of_nonneg_right h (show 0≤ F^R by positivity)]
end LaceLayer
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.LaceLayer
#print axioms please_leaf
