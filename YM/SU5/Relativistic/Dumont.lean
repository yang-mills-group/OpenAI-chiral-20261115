import YM.SU5.Relativistic.Crotch
import YM.SU5.Relativistic.Reptile
/-! # Purchases, keeping track of M horizon; checking real estimate on the chosen course. Includes raw power bill. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.ScreeV
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner

private lemma tender_g(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
open CF.Papyrus.Franc CF.Papyrus.Franc.Loaves CF.Papyrus.Franc.Meshy
open CF.Crest CF.Crest.Sleet CF.Crest.Sleet.UpStart
open Satin Tapestry Tower.SlabMark
variable {T S:Finset Cover}{K0 K':ℕ}{η:ℝ}
local notation "K"=>tent Y H
-- any x of moved geometry halo.Layout. Need exist i-axis Tone.
private lemma situate (i:Axis)(S:Finset Cover):∃ x:ℤ,∃ v s:ℕ,∃ X:Cover, Between (tent Y H) i 0 (ruler P.block * (heightB v:ℕ)) (plow (tent Y H) i x S)∧ Transom i (plow (tent Y H) i x S) X s:=by
 let A(x:Cover):=univ.sup fun i:Axis=> (x i).natAbs; let T:=S.sup A; have he(x:Cover)(p:x∈S)(j:Axis): - (T:ℤ) ≤ x j ∧ x j≤ T:=by have hx:= (le_sup (s:=Finset.univ) (b:=j) (f:=fun i:Axis=> (x i).natAbs) (mem_univ j)).trans (Finset.le_sup (f:=A) p); omega
 let q:=T+(tent Y H).ℓ; let b:=ruler (tent Y H).B; let X:=plow K i q S
 have hp:Between K i (-(q:ℤ)) (q:ℤ) S:=fun j t=>by obtain ⟨v,h⟩:=he j t i; unfold q; omega
 have hs:= hp.relocate K i q; refine ⟨q,q,2*T,fun _=> -(T:ℤ),fun x p=>?_, (show Transom i X (fun _=> -↑T) (2*T) from ?_)⟩
 · obtain ⟨x,i'⟩:=hs x p; have hx:0≤b* q+ -(q:ℤ):=by have h:1≤b:=ruler_gene _; nlinarith only [mul_le_mul_of_nonneg_right h (show 0≤(q:ℤ) by positivity)]
   constructor; · unfold b at hx; omega
   apply i'.trans; change b*(q:ℤ)+q≤ b*(↑(heightB q):ℤ); unfold heightB; push_cast; nlinarith only [mul_le_mul_of_nonneg_right (show (1:ℤ)≤b from ruler_gene _) (show 0≤(q:ℤ) by omega), show 1≤b from ruler_gene _]
 intro j u z a; obtain ⟨x,h,rfl⟩:= plow_stays _ _ _ _ a; rw [Tower.SlabMark.moves,if_neg u]; obtain ⟨v,t⟩:=he x h j; change -(T:ℤ) ≤ x j ∧ _; dsimp only; omega
variable {L_:List Wine} {Z Z':ℝ}
open Loaves
def fiz (Jp:Calibration) (z:ℂ)(L':List Wine): Buffered.Family Jp := 1+z • (dek Jp L'+(-tallyW L') • 1)
private lemma swayH {I:Type*} [LinearOrder I][Fintype I]{A B:Op I}(M:Op I)(k:ℕ) (a:IsStarProjection A)(b:IsStarProjection B)(h:A=B): Saber (B:=M) a k= Saber (B:=M) b k:=by subst B; rfl
-- Cow for voter. ℓ. requires *assert* sP Olymp at each period. Not Pt txn.
lemma vintageW (U_: FairRoute P.P P.J P.h P.N0 Chi.canonical)(p_:Inflation Z P)(v:S.Nonempty)(g:0<ε)
    (c:AreaW false S L_)(u:InTest (tent Y H) false S false (dek (tent Y H) L_))(h:Tower.CovCover (tent Y H) (dek (tent Y H) L_))
    (φ:CF.Papyrus.Franc.postage P.K.j Z')(x0:0≤Z')(zH: CF.Papyrus.Franc.charge Z'≤ P.h)
    (q:P.d ≤ δ)(f:∃ N:ℕ,∀ η>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter P.K.j δ n γ w η)(mK:∀ᶠ n:ℕ in atTop,∀ N:Side,n≤N.val→∀ M:Tulip.Male, Meshy.Muster P.d N M) (j:Axis): ∃ ζ> (0:ℝ),∀ z:ℂ,0<‖z‖→‖z‖≤ζ→∃ a:ℤ,∃ T:Finset Cover,∃ b:ℕ,0<b ∧ let D:=relocate (tent Y H) j a (fiz (tent Y H) z L_); InTest (tent Y H) true T false D ∧ Between (tent Y H) j 0 (ruler P.block * (b:ℤ)) T ∧∀ᶠ s:ℕ in atTop, ∀ n:ℕ,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop, ‖sharp Y H s i k (thicket (tent Y H) j b D n)‖ ≤ Real.exp ((staveP n:ℝ)*(5*(ε*‖z‖))) :=by
 obtain ⟨N,F⟩:= f; have f4:∀ η> (0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter 4 δ n γ w η:= P.kJ ▸ F
 obtain ⟨a,d,X⟩:= audience (P.dpos.le.trans q) f4 v ε g c; refine ⟨a,d,fun z t x=>?_⟩
 obtain ⟨W,p,η,hη,q0,vT⟩:= X z t x; let V:=ε*‖z‖; have he:0<V:=mul_pos g t
 obtain ⟨s,T,B,C0,g',hX⟩:= situate Y H j W
 let H₀:=heightB T; let Gc0:=fiz K z L_; let n0:=plow K j s W; let D:= relocate K j s Gc0
 have hx:InTest K true W false Gc0:= (((InTest.one).add (((u).add ((InTest.one).smul _)).smul _)).mono p).widen -- tune constructor order
 have hy:Tower.CovCover K Gc0:= (Tower.covariant_parts K ((Tower.covariant_one K)) (Tower.covariant_scale K ((Tower.covariant_parts K h (Tower.covariant_scale K (Tower.covariant_one K) _)).1) _)).1
 have hb:InTest K true n0 false D:= Tower.flow_port K j _ hx
 refine ⟨s,n0,H₀,by unfold H₀ heightB; positivity, hb,g',?_⟩
 let r:= V *heels P.block (addgap K) B T; have hl:0<r:=mul_pos he (inv_pos.mpr (by exact_mod_cast heel_pos (A:=T) (U:=B) (S:=P.block) addgap_pos))
 obtain ⟨m,pm,v'⟩:= ((arnica Y U_ p_ φ zH x0 q ⟨N,F⟩ r hl).and vT).exists
 obtain ⟨γ,kH,H_A,k_σ,F0⟩:=v'; obtain ⟨A,ht,wp⟩:=glory m; obtain ⟨C,hC,vC⟩:= dinnerC L_ c A z ht -- pS args order? signature
 obtain ⟨o,v⟩:=v; obtain ⟨τ,hτ,N',u',uT,E⟩:= icon (δx:=P.J.n) (s:=P.d) (η:=η) (r:=V) («K»:=m) (v:=p v) c (W:=H_A) p kH q vC
 obtain ⟨N0,hN⟩:=mK.exists
 have hz:Tendsto (temp ∘ hat P.R.L P.x) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 let Z:= C*(4*(u'+u'+1)^4:ℕ)
 filter_upwards [pm Z (by unfold Z; positivity), hz.eventually (ge_mem_nhds hτ),hz.eventually (ge_mem_nhds P.J.ht)] with s' gS hS hS' n
 obtain ⟨T0,b0,r0,h'T,F',kF⟩:= Polder.express (show 0<H₀ by unfold H₀ heightB; positivity) g' C0 hX hb n
 let lB:= b0+N+N'+k_σ+N0 + singleTick K T*staveP n +addgap K+(B+addgap K)
 filter_upwards [gS,(count_grows Y s').eventually_ge_atTop lB] with i mB hk
 let Λ:=count Y s' i; let κ:= momentm Y i s'; have hk0:(tent Y H).c κ=Λ:=terrain ..
 let Z':=thicket K j H₀ D n; let V0:=max 1 C; let B':=V0^((More Λ).val^4); have hh:0<B':=pow_pos (zero_lt_one.trans_le (le_max_left ..)) _
 filter_upwards [ferry_later Y s' i,(tide_M Y s' i).eventually_ge_atTop k_σ, thaw_plot Y (V/B') (div_pos he hh) s'] with k P' Hk Υ
 let I:= gram Y s' i k; let M:= I.J.M; have hx':I.p.threshold=temp (hat P.R.L P.x s'):= (congrArg BudgetPoint.threshold (prices_plot Y s' i k P'.enters).1).trans (Y.meter.boot s').1
 let R:=(compass Y i k s'); let Y':=solder Y i k P'.depth s'; let P0:= tender_g Y H s' i k P'; have vN: lB≤Λ.val:=hk
 unfold lB at vN
 have hs':Meshy.Muster P.d Λ M:=hN _ (by omega) M
 have ep:(0:ℤ)+ (H₀:ℤ)*ruler (tent Y H).B*↑(staveP n)+ ↑(addgap K)≤ Λ.val:=by
    have he:(H₀:ℤ)*ruler (tent Y H).B=singleTick K T:=by unfold H₀ singleTick ruler; push_cast; ring
    rw [zero_add, he]; exact_mod_cast show singleTick K T *staveP n+addgap K≤Λ.val from by omega
 rw [actualRead]; change ‖R (arrange _ _ hk0 _)‖ ≤_
 refine curr n R Y' j hk0.symm P0 hs' H₀ (by rw [zero_add] at ep; exact ep) (by change B + addgap (tent Y H) ≤ Λ.val; omega) T rfl he (k:=m) (p:=P.d) (w:=H_A) (d:=u') (B:=A) (η:=η) (τ:=I.p.threshold) (C:=C) ?_ ?_ T0 Z' r0 C0 h'T ?_
 · intro L U t
   let C':=probe L; let D:=(L.length:ℝ)*(V+V)
   have hv: WardP Y s' i k m D Z C':=by
      intro x G Px P0x; have hG:spar 4 M G=Px:=by unfold Px; rw [P.kJ]
      have vv:= (safety Y s' i k x).2
      have hv:= turrV wp (roofage Y i s') (show I.p.threshold ≤ P.J.k from hx' ▸ hS') uT hη.le hC U x (changeM P.U G M) (hG.symm ▸ P0x) (hG.symm ▸ (show Sea Px (changeM P.U G M) from vv)) he.le q0
      obtain ⟨T,E,e1,e2,e3,e4⟩:=hv; refine ⟨T,E,e1,e2,e3,?_⟩; rw [show Saber (B:=tickA _) P0x m= Saber (B:=tickA Λ) (P:=spar 4 M G) ((hG.symm ▸ P0x)) m from ?_]; exact e4
      exact swayH _ _ _ _ hG.symm
   have hy: ‖R C'‖ ≤ Real.exp (D+r*sites Λ):=mB k P'.depth P'.enters C' D (U.permit (Finset.Subset.refl _)).env hv
   apply hy.trans; apply Real.exp_monotone; change _≤_; unfold D r; change heels P.block (addgap K) B T*sites Λ ≤ (L.length:ℝ) at t; nlinarith only [mul_le_mul_of_nonneg_left t he.le]
   -- order goal nested fix
 · intro L U
   have hf:L.length ≤(More Λ).val^4:= U.pcount; have ht:∀ x,‖probe L x‖≤B':= fun x=> (U.actual hC ht x).trans ((pow_le_pow_left₀ hC.le (le_max_right 1 _) _).trans (pow_le_pow_right₀ (le_max_left ..) hf))
   exact (show ‖R (probe L)-Y' (probe L)‖≤ (V/B')*B' from Υ i P'.depth _ B' (U.permit (Finset.Subset.refl _)).env ht).trans_eq (div_mul_cancel₀ _ hh.ne')
 let W':=(mud L_ z o W ((tent Y H).c κ)); have hs:Meshy.Muster P.d ((tent Y H).c κ) M:=hN _ (by rw [hk0]; omega) M
 have hbi:Galop K Gc0 W 1 κ m M H_A u' P.d I.p.threshold η V C A:=by
    let V₁:= (tent Y H).c κ; have hA : Brace.Sparkle V₁ P.d M 4 := by unfold V₁; rw [hk0,←P.kJ]; exact P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s').size) _
    have hE:Even V₁.val:=by let X:=Vale.mesh κ P.R.L 0; change Even (X.val*2*P.block.val); exact ⟨X.val*P.block.val,by ring⟩
    have hf: Crisp M m H_A u' P.d I.p.threshold η V C A W':=E _ (by change _ ≤ V₁.val; unfold V₁; rw [hk0]; omega) M _ I.p.threshold_pos.le (hx' ▸ hS) (F0 V₁ (by unfold V₁; rw [hk0]; omega) (by unfold V₁; rw [hk0]; omega) hE M Hk (hA.projection _ (guard0 P.dpos.le))) hA (hy κ) (hx.support _)
    refine ⟨[W'],rfl,?_,?_,Battalion.alone hf⟩
    · change W'.broad∪∅⊆_; simp; exact Finset.Subset.refl _
    rw [probe_cons,CF.Pannier.Chancel.Cliplet.probe_nil,mul_one]; rfl
 apply kF κ (by rw [hk0]; omega) _ _ _ _ _ _ _ _ _ _ hs (Galop.migrate hbi j s hs)
end Papal
end LocalLimit
end Rate
end YM.CF.Py
