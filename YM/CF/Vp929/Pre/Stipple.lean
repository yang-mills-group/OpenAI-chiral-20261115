import YM.CF.Vp929.Pre.Extras
import YM.CF.Vp929.Pre.Azure
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
local notation "F₁"=> Folk S' z' (Words S')
local notation "V_"=> Troupe S' z' (Words S')
local notation "Xo" => Hos S' z'

open Lich Iva
variable {F:Corr (Scree.mid n B)}
variable {Pν: ↥(Sil (w.step V) (coming D.Z 105 5*radiusB x))}{N0:ℕ}
local notation "Δ"=> (o.muster.post+90)*radiusB x
local notation "Ξ"=> (o.muster.loft+o.muster.post+200)*radiusB x
local notation "D'"=> Dwell ι
local notation "Xp"=> (stake (n:=LeanV (Tulip.Single (Scree.mid m B))) h)
local notation "FX"=> F₁→Raid (Dwell (Scree.mid m B))
open Engine Engine.Basin Engine.Docket Dialect
local notation "T_"=> Troupe S' z' (Words S')
local notation "Lo"=> Palot.leaf (Site (Domain m B))
local notation "De"=> T_→ Lo→ Raid D'
local notation "PZ"=> T_→Lo→ Orbit ι→ Cipher ι
local notation "oWell"=> o.muster
local notation "Loχ"=> Palot.leaf (Site (Domain m B))
local notation "Px"=> V_→Loχ→ Orbit ι→ Cipher ι
local notation "Kx"=> V_→ Loχ→ Raid (Scree.Dwell ι)
open Vow Bake Salt Stax Sour Larch
local notation "Θ'" t:max=> (cook S' (Finset.toLeft t)).flags
local notation "δ_"=> (cipherK J.n)
local notation "U_"=> (fullD (n:=ι))
variable {t bL σ κ Bv:ℝ}{nₐ:ℕ}{pW:WindV K.j 2}
variable {Z:Cellar N0 o p p' c f ag Cg} {M:Climate D.pilot R c x t bL σ κ ag Cg Bv nₐ}
namespace Focus
variable (Uq:Focus Z M pW ff)(Ty:Ids (Scree.mid m B))
local notation "Upp"=> ((tolQ p).supportExponent)
variable (Q:β∈ Year R x)(hF:Charged p' w.input K.j R.L.val h f F)
local notation "Ys'"=> Ys β F
local notation "Υ'"=> Xs β
local notation "F_"=> (Z.toLid.crew β Q).1
local notation "A0"=> (Z.toLid.choice Q (gross_shape hF (le_refl f)))
variable {Lz:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Orbit (Scree.mid m B)→Cipher (Scree.mid m B)}{Cp:Troupe (w.step V) (coming D.Z 105 5*radiusB x) (Words (w.step V))→ Aura (Scree.mid m B)→ Raid (Scree.Dwell (Scree.mid m B))}
variable (hv:Rill.Arch w.G d) (hm:hv.val=1){γ:ℝ}
variable (hγ:Fair p R x κ γ σ)(tF:Charged p' w.input K.j R.L.val h ff F)
abbrev noncash_E (Vq:Rill.Arch w.G d)(E:Corr (Scree.mid n B)):= Lunar.radixLin (p:=p) (p':=p') (o:=o) Vq (Lunar.pennies E.1)
abbrev noncash_A (Vq:Rill.Arch w.G d)(E:Corr (Scree.mid n B)):= Lunar.roseLin (p:=p) (p':=p') (o:=o) Vq (Lunar.pennies E.1)
abbrev pre_E (L:Px)(E:Corr η): RegBudget ι:= tapped p o Ty L+noncash_E (p:=p) (p':=p') (o:=o) hv E
abbrev pre_A (L:Px)(E:Corr η): Cusp ι:= Cash.owe Ty (slipP p L)+ noncash_A (p:=p) (p':=p') (o:=o) hv E
abbrev paceM(R:Patch)(c:Estimate)(Pay x ff:ℝ):= pace_Z R (Pay*gritY R.L.val) ff (c.small x)
abbrev sharpA(R:Patch)(c:Estimate)(Pay x h ff:ℝ):= pack_Q 6 *pay_Z 2 (radiusB x) 5 6 x h (c.F x) (paceM R c Pay x ff) 1+(c.Xr x+3*c.Qh x)
abbrev sharpE(R:Patch)(c:Estimate)(C_t A Pay x ρ h ff:ℝ):= wren_K 6 2 * (paceM R c Pay x ff+rise_K 6 2 1*|way_Q R 6 2 x ff (population*(A*followV [] R.L)) (min 1 (ρ/4)) C_t h|)+reserveT 2 6 (radiusB x) 1*(6*c.Qh x)
local notation "T₀" x:max F:max=> pre_E (p:=p) (p':=p') (o:=o) Ty hv x F
local notation "Aρ" x:max F:max=> pre_A (p:=p) (p':=p') (o:=o) Ty hv x F
local notation "X₁"=> Banker.PhiM Z β F
local notation "pA"=> (sharpA R c Pay x h ff)
local notation "pE"=> (sharpE R c pW.C A Pay x ρ h ff)
local notation "BU"=> (Cash.prominence p)
structure CostsPaid (L:PZ)(p:BudgetPoint)(G:RegBudget ι)(K:Cusp ι)(h HS LK e α:ℝ) :Prop where
 emptyC : MonoQ p h (p.supportExponent+1+1+1) (nixV (cone_f L)) HS
 mark : Marked p h (p.supportExponent+1+1+1) (cone_f L) LK
 claim : DuesQ Utrue p h G e
 buys : Packed p h (p.supportExponent+1+1) K α
structure EState (p:BudgetPoint)(L:PZ)(o:Pitching w D x) (Ty: Ids (Scree.mid m B))(A₀:RegBudget ι)(K:Cusp ι)(k l X Y:ℝ) :Prop where
 spirit : Spirit p o L Ty
 priced : CostsPaid L p A₀ K h k l X Y
 sell : PreR p (cone_f L) A₀ K (Cash.summit Ty (slipP p L)) h Y X
 zeal : ZealQ K
include Uq Q hγ tF hm
local notation "ℓ'"=> Ledge nₐ t (Scales.y SU.group R.L x)
lemma master : EState p X₁ o Ty (T₀ X₁ F) (Aρ X₁ F) (c.H x) (c.Fκ x) pE pA:=by
 obtain ⟨T,g,E,G,Bx,q,e,V₀,dμ,x'⟩:= Uq.sharp Ty Q tF
 have pB:Bx=hv:= Subtype.ext (q.trans hm.symm); subst Bx
 let g':=yieldsSpirit Uq Ty Q (tF.mono Uq.cost) Z.master_pond g
 obtain ⟨A,C,L,u,v,w,s,ha,_,_,_,_,wQ,hu⟩:=V₀.render
 obtain ⟨U₀,A₁⟩:= Lunar.turn_L Ty hv E G e
 let Y:= slipP p X₁; have hp:T₀ X₁ F= writ_E E+cast_E (curr_X p (old_Q X₁) (nixV (cone_f X₁)) (1,Ty)) Ty:= by rw [U₀]; change writ_E _ + Cash.earn Ty p Y + _ = writ_E _ + noncash_E (p:=p) (p':=p') (o:=o) hv F + Cash.earn Ty p Y; abel
 have he:Aρ X₁ F= writ_K G+nextE (curr_r p (old_Q X₁) (nixV (cone_f X₁)) (1,Ty)):=by rw [A₁]; exact add_comm ..
 rw [hp,he]; refine ⟨g',⟨⟨A,v,fun x=>Sour.dutyK (P:=p) u x⟩,⟨_,fun i D x=> dμ.price i D (mem_filter.mp x).2.1 (mem_filter.mp x).2.2,x'⟩,wQ,C,w,s⟩,⟨wQ,hu⟩,ha⟩
omit tF hm Q hγ
lemma arch_exists (τ:Ids (Scree.mid m B)): ∃ hV:Rill.Arch w.G d,hV.val=1:= by
 let y:= Scales.y SU.group R.L x; let f:Corr η:=0; let h0: Charged p' w.input K.j R.L.val h ff f:= Charged.zero.mono Uq.buy.le; obtain ⟨_,_,_,_,V,v,_⟩:=Uq.sharp τ Z.toLid.living h0; exact ⟨_,v⟩
abbrev pivotV (τ:Ids (Scree.mid m B)):= (Uq.arch_exists τ).choose
include Q tF hγ hm
local notation "Xκ"=> (Banker.Phi Z (β:ℂ) F)
local notation "Ψs"=> (shiftW R x κ σ γ)
local notation "WE"=> (coinW R x κ (2*σ) (shiftW R x κ σ γ))
def moreE(R:Patch)(x κ γ σ:ℝ):= coinW R x κ (2*σ) (shiftW R x κ σ γ)
def moreF(R:Patch)(x κ σ:ℝ):= burnQ R x κ (2*σ)
-- Promotion of costs plus the real-plane identity via coldE.
lemma live_state (hvβ:(β:ℂ) ∈ ℓ'): EState p Xκ o Ty (T₀ Xκ F) (Aρ Xκ F) (c.H x+moreF R x κ σ) (c.Fκ x+moreF R x κ σ) (pE+moreE R x κ γ σ) (pA+Ψs) := by
 let Pp:= gross_shape (D:=D) tF Uq.cost; obtain ⟨T,g⟩:=Banker.oldAcquire Z Pp Q M; obtain ⟨X,hX⟩:=Banker.Hoisted Z Pp M hvβ; obtain ⟨Y,fY⟩:=Banker.diffAcquire Z Pp Q M hvβ; let Hm:= Uq.master Ty Q hv hm hγ tF
 let Vg:= Banker.trustI Z Pp Q M X hvβ hX; let Ho:= Banker.trustO Z Pp Q M T g; let Ft:= tF.mono Uq.cost; let zoom:= @Z.pond (Z.toLid.scaler Q); let hs:= Uq.yieldsSpirit Ty Q Ft zoom Vg
 obtain ⟨hV,hW,hA⟩:= differs Uq Ty hγ (α:=hX) hs (X₁) Hm.spirit T Y g fY; let P:= Young Uq (Spirit.minus Ty hs X₁ Hm.spirit).seed fY
 have hT:T₀ Xκ F-T₀ X₁ F=tapped p o Ty Xκ-tapped p o Ty X₁:=by unfold pre_E; abel
 have Aψ:Aρ Xκ F - Aρ X₁ F =Cash.owe Ty (slipP p Xκ)-Cash.owe Ty (slipP p X₁):=by unfold pre_A; abel
 have lam :∀ (H:Type)[AddCommGroup H](a b:H), a=b+(a-b):= by intros; abel
 have ηx : ZealQ (Aρ Xκ F):= by rw [lam _ (Aρ Xκ F) (Aρ X₁ F),Aψ]; exact Cash.zealAdd Hm.zeal (Cash.zealSub (Cash.zealO _) (Cash.zealO _))
 have ht:DuesQ Utrue p h (T₀ Xκ F) (pE+WE):=by rw [lam _ (T₀ Xκ F) (T₀ X₁ F),hT]; exact Ione.addT p Hm.priced.claim hW
 refine ⟨hs,⟨?_ ,?_ ,ht,?_⟩,⟨ht,fun V₁ k=>?_⟩,ηx⟩
 · have H:=P.1; rw [coneSub] at H; rw [lam _ (nixV (cone_f Xκ)) (nixV (cone_f X₁))]; exact Hm.priced.emptyC.add H
 · have H:=P.2.1; rw [coneSub] at H; rw [lam _ (cone_f Xκ) (cone_f X₁)]; exact Hm.priced.mark.add H
 · rw [lam _ (Aρ Xκ F) (Aρ X₁ F),Aψ]; exact Hm.priced.buys.add hA
 let H:= Hm.sell.sell V₁ k; let LE:= noncash_E (p:=p) (p':=p') (o:=o) hv F; let LA:= noncash_A (p:=p) (p':=p') (o:=o) hv F; let Vn(S:PZ):= Cash.earn Ty p (slipP p S)
 let C (S:PZ):= coldE p (FeeD p (nixV (cone_f S))) V₁; let y:= exponentL p LE V₁.1+ fuelV p LA V₁
 have yE (L:PZ)(h:Cash.poise (slipP p L))(J:exponentL p (writ_E (Placement o Ty L)) V₁.1=coldE p (old_Q L) V₁) : C L+y= owed_E ι (Cash.summit Ty (slipP p L))+exponentL p (T₀ L F) V₁.1+fuelV p (Aρ L F) V₁:= by
     let U:=(Cash.budgetIdentity (P:=p) Ty h V₁ k); unfold C y pre_E pre_A tapped; rw [show FeeD _ (nixV (cone_f L))= old_Q L+slipP p L from lam .., crep]; change _=_+exponentL p ((writ_E _+Vn L)+LE) V₁.1+fuelV p (Cash.owe Ty _+LA) V₁; rw [ripe_H p V₁,ripe_H p V₁,Vow.toast, U,J]; abel
 have t:= yE X₁ (Hm.spirit.livelihood Uq Ty hγ g zero_le_one (by norm_num)).1 (pactSold Uq Ty Q Ft Z.master_pond Ho V₁ k); have hz := yE Xκ (hs.livelihood Uq Ty hγ hX zero_le_one (by norm_num)|>.1) (pactSold Uq Ty Q Ft zoom Vg V₁ k);
 apply Eq.trans _ hz; have hy: y=0:= add_left_cancel ((t.trans H.symm).trans (add_zero (C X₁)).symm); rw [hy,add_zero]
end Focus
end Pitching
end YM.CF.Py.Rate
