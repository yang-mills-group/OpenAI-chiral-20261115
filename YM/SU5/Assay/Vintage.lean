import YM.SU5.Relativistic.Dumont
import YM.SU5.Assay.Arnica
import YM.SU5.Assay.ArenaFlags
/-! Checker version of Relativistic/Dumont, paying on Geometry. -/
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
open CF.Papyrus.Franc CF.Papyrus.Franc.Loaves CF.Papyrus.Franc.Meshy
open CF.Crest CF.Crest.Sleet CF.Crest.Sleet.UpStart
open Satin Tapestry Tower.SlabMark
variable {T S:Finset Cover}{K0 K':ℕ}{η:ℝ}
local notation "K"=>tent Y H
open Tower.SlabMark.Etch
variable {L_:List Wine} {Z' ε δ:ℝ}
open Loaves

lemma tide_uniform (s b:ℕ): ∀ᶠ k:ℕ in atTop,∀ i:ℕ,b≤(gram Y s i k).J.M.val.val:=by
 let f (s i k:ℕ):=(gram Y s i k).J.M
 have hp (s i k:ℕ)(v:s < Y.uv k): f s i k= upMale P.R.L P.R.odd_side (f (s+1) i k):=by
    let X:= (Y.voyage i).X (Y.uv k); change (X.gram s).J.M=upMale P.R.L P.R.odd_side (X.gram (s+1)).J.M
    rw [← (X.pull.owns s v.le).taste,← (X.pull.owns (s+1) v).taste]; exact ((P.W.arm _ (Y.uv k)).pass s v).grown
 filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+b)] with k u i; change b ≤ (f s i k).val.val
 induction b generalizing s with
 | zero=> simp
 | succ b ih=>
    have hv:= ih (s+1) (by omega); rw [hp s i k (by omega)]; change b+1 ≤ P.R.L.val*(f (s+1) i k).val.val
    have he:= P.R.coarse; let X:=(f (s+1) i k).val.val; have p:0<X:=(f (s+1) i k).val.property
    change b≤X at hv; change _ ≤ _ * X; have ht:= Nat.mul_le_mul_right X he; omega

def coSeat (j:Axis)(w:ℕ):Cover:=fun i=> if i=j then 0 else -(w:ℤ)
private lemma assay_room (S:Finset Cover): ∃ w:ℕ,0<w ∧ ∀i,Between K i (-ruler P.block*w) (ruler P.block*w) S :=by
 let A(x:Cover):=univ.sup fun i:Axis=> (x i).natAbs; let T:=S.sup A; have he(x:Cover)(p:x∈S)(j:Axis): - (T:ℤ) ≤ x j ∧ x j≤ T:=by have hx:= (le_sup (s:=Finset.univ) (b:=j) (f:=fun i:Axis=> (x i).natAbs) (mem_univ j)).trans (Finset.le_sup (f:=A) p); omega
 let q:= 1+T+(tent Y H).ℓ; have hg:1≤ ruler P.block:=ruler_gene _
 refine ⟨q,by unfold q; omega,fun i x u=> ?_⟩
 obtain ⟨v,t⟩:=he x u i; have h : (q:ℤ)≤ruler P.block*q:=le_mul_of_one_le_left (by positivity) hg
 rw [neg_mul]; unfold q at *; constructor <;> omega
lemma seated (w:ℕ)(j:Axis)(S:Finset Cover)(t:∀i, Between (tent Y H) i (-ruler P.block*w) (ruler P.block*w) S):
  House (tent Y H) ((w+w:ℕ):ℤ) (coSeat j w) 0 (plow (tent Y H) j w S):=by
 intro i
 by_cases h:i=j
 · subst i; have g:= Between.relocate K j (t j) w
   rw [show (K).B=P.block from rfl,neg_mul,add_neg_cancel] at g
   simpa [runnel,coSeat,show (K).B=P.block from rfl,mul_add] using g
 intro x y; obtain ⟨x,v,rfl⟩:=plow_stays _ _ _ _ y; rw [Tower.SlabMark.moves,if_neg h]
 simpa [runnel,coSeat,show (K).B=P.block from rfl,h,mul_neg,neg_mul,← add_assoc] using t i x v

private lemma assay_swayH {I:Type*} [LinearOrder I][Fintype I]{A B:Op I}(M:Op I)(k:ℕ) (a:IsStarProjection A)(b:IsStarProjection B)(h:A=B): Saber (B:=M) a k= Saber (B:=M) b k:=by subst B; rfl
/-- Extra latch n bounds the UV-index independently of period (for fixed height),
 assuming ferry itself. Width independent of height. -/

lemma vintageG (p_:Geometry P)(v:S.Nonempty)(g:0<ε)
    (c:AreaW false S L_)(u:InTest (tent Y H) false S false (dek (tent Y H) L_))(h:Tower.CovCover (tent Y H) (dek (tent Y H) L_))
    (φ:CF.Papyrus.Franc.postage P.K.j Z')(x0:0≤Z')(zH: CF.Papyrus.Franc.charge Z'≤ P.h)
    (q:P.d ≤ δ)(f:∃ N:ℕ,∀ η>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter P.K.j δ n γ w η)(mK:∀ᶠ n:ℕ in atTop,∀ N:Side,n≤N.val→∀ M:Tulip.Male, Meshy.Muster P.d N M) (j:Axis): ∃ ζ> (0:ℝ),∀ z:ℂ,0<‖z‖→‖z‖≤ζ→∃ (W:Finset Cover)(w:ℕ),S⊆W∧0<w ∧ (∀i,Between K i (-ruler P.block*w) (ruler P.block*w) W)∧
    ∀ᶠ s in atTop,∃n:ℕ,∀ᶠ i:ℕ in atTop,∀ k:ℕ,n≤k→ Ferry Y s i k →
      Mosaic (w+w:ℕ) (coSeat j w) (slideN Y s (w+w) i) (relocate K j w (fiz K z L_)) (Real.exp (3*(ε*‖z‖))) (sharp Y H s i k):=by
 obtain ⟨N,F⟩:= f; have f4:∀ η> (0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N≤n.val→Winter 4 δ n γ w η:= P.kJ ▸ F
 obtain ⟨a,d,X⟩:= audience (P.dpos.le.trans q) f4 v ε g c; refine ⟨a,d,fun z t x=>?_⟩
 obtain ⟨W,p,η,hη,q0,vT⟩:= X z t x; let V:=ε*‖z‖; have he:0<V:=mul_pos g t
 obtain ⟨w,hw,t0⟩:= assay_room Y H W; refine ⟨W,w,p,hw,t0,?_⟩
 let Gc0:=fiz K z L_; let H₀:=w+w; let n0:=plow K j w W; let D:= relocate K j w Gc0
 have hx:InTest K true W false Gc0:= (((InTest.one).add (((u).add ((InTest.one).smul _)).smul _)).mono p).widen -- tune constructor order
 have hy:Tower.CovCover K Gc0:= (Tower.covariant_parts K ((Tower.covariant_one K)) (Tower.covariant_scale K ((Tower.covariant_parts K h (Tower.covariant_scale K (Tower.covariant_one K) _)).1) _)).1
 have hhs: House K H₀ (coSeat j w) 0 n0:= seated Y H w j W t0
 let r:= V *((Etch.ratio P.block H₀:ℕ):ℝ)⁻¹; have hl:0<r:=mul_pos he (inv_pos.mpr (by exact_mod_cast ratio_pos P.block (add_pos hw hw)))
 obtain ⟨m,pm,v'⟩:= ((arnicaG Y p_ φ zH x0 q ⟨N,F⟩ r hl).and vT).exists
 obtain ⟨γ,kH,H_A,k_σ,F0⟩:=v'; obtain ⟨A,ht,wp⟩:=glory m; obtain ⟨C,hC,vC⟩:= dinnerC L_ c A z ht -- pS args order? signature
 obtain ⟨o,v⟩:=v; obtain ⟨τ,hτ,N',u',uT,E⟩:= icon (δx:=P.J.n) (s:=P.d) (η:=η) (r:=V) («K»:=m) (v:=p v) c (W:=H_A) p kH q vC
 obtain ⟨N0,hN⟩:=mK.exists
 have hz:Tendsto (temp ∘ hat P.R.L P.x) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 let Z:= C*(4*(u'+u'+1)^4:ℕ)
 filter_upwards [pm Z (by unfold Z; positivity), hz.eventually (ge_mem_nhds hτ),hz.eventually (ge_mem_nhds P.J.ht)] with s' gS hS hS'
 obtain ⟨n,e⟩:=eventually_atTop.mp (tide_uniform Y s' k_σ)
 refine ⟨n,?_⟩
 let lB:= N+N'+k_σ+N0 + 2*Etch.pitch P.block H₀
 filter_upwards [gS,(count_grows Y s').eventually_ge_atTop lB] with i mB hk k hnk P'
 have Hk:=e k hnk i
 let Λ:=count Y s' i; let κ:= momentm Y i s'; have hk0:(tent Y H).c κ=Λ:=terrain ..
 let I:= gram Y s' i k; let M:= I.J.M; have hx':I.p.threshold=temp (hat P.R.L P.x s'):= (congrArg BudgetPoint.threshold (prices_plot Y s' i k P'.enters).1).trans (Y.meter.boot s').1
 let R:=compass Y i k s'; have vN:lB≤Λ.val:=hk
 unfold lB at vN
 let W':=(mud L_ z o W ((tent Y H).c κ)); have hs:Meshy.Muster P.d ((tent Y H).c κ) M:=hN _ (by rw [hk0]; omega) M
 have hbi:Galop K Gc0 W 1 κ m M H_A u' P.d I.p.threshold η V C A:=by
    let V₁:= (tent Y H).c κ; have hA : Brace.Sparkle V₁ P.d M 4 := by unfold V₁; rw [hk0,←P.kJ]; exact P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s').size) _
    have hE:Even V₁.val:=by let X:=Vale.mesh κ P.R.L 0; change Even (X.val*2*P.block.val); exact ⟨X.val*P.block.val,by ring⟩
    have hf: Crisp M m H_A u' P.d I.p.threshold η V C A W':=E _ (by change _ ≤ V₁.val; unfold V₁; rw [hk0]; omega) M _ I.p.threshold_pos.le (hx' ▸ hS) (F0 V₁ (by unfold V₁; rw [hk0]; omega) (by unfold V₁; rw [hk0]; omega) hE M Hk (hA.projection _ (guard0 P.dpos.le))) hA (hy κ) (hx.support _)
    refine ⟨[W'],rfl,?_,?_,Battalion.alone hf⟩
    · change W'.broad∪∅⊆_; simp; exact Finset.Subset.refl _
    rw [probe_cons,CF.Pannier.Chancel.Cliplet.probe_nil,mul_one]; rfl
 have GA:Galop K D n0 1 κ m M H_A u' P.d I.p.threshold η V C A:=Galop.migrate hbi j w hs
 have heq:sharp Y H s' i k=(fun f=> R (Tapestry.arrange _ _ hk0 (f κ))):=funext (fun f=>actualRead Y H s' i k _)
 rw [heq]
 have gs:Proscenium (tent Y H).B H₀ ((tent Y H).c κ) (slideN Y s' H₀ i):=by
   rw [hk0]
   exact proscenium (B:=P.block) (N:=Λ) (w:=H₀) (add_pos hw hw) (by omega)
 refine Galop.mosaic GA hs hhs gs Λ hk0 R ?_
 · intro L U t
   let C':=probe L; let D:=(L.length:ℝ)*(V+V)
   have hv: WardP Y s' i k m D Z C':=by
      intro x G Px P0x; have hG:spar 4 M G=Px:=by unfold Px; rw [P.kJ]
      have vv:= (safety Y s' i k x).2
      have hv:= turrV wp (roofage Y i s') (show I.p.threshold ≤ P.J.k from hx' ▸ hS') uT hη.le hC U x (changeM P.U G M) (hG.symm ▸ P0x) (hG.symm ▸ (show Sea Px (changeM P.U G M) from vv)) he.le q0
      obtain ⟨T,E,e1,e2,e3,e4⟩:=hv; refine ⟨T,E,e1,e2,e3,?_⟩; rw [show Saber (B:=tickA _) P0x m= Saber (B:=tickA Λ) (P:=spar 4 M G) ((hG.symm ▸ P0x)) m from ?_]; exact e4
      exact assay_swayH _ _ _ _ hG.symm
   have hy: ‖R C'‖ ≤ Real.exp (D+r*sites Λ):=mB k P'.depth P'.enters C' D (U.permit (Finset.Subset.refl _)).env hv
   apply hy.trans; apply Real.exp_monotone; unfold D r; change ((Etch.ratio P.block H₀:ℕ):ℝ)⁻¹*sites Λ ≤ (L.length:ℝ) at t; nlinarith only [mul_le_mul_of_nonneg_left t he.le]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.vintageG
