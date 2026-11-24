import YM.CF.Lor.Haven
/-! Replacement for Lor.Haven.payer_f; DON’T use old API (hypothesis quantified over order zero `Before`, cannot instantiate!). Here use `Push.Uniform.pre_order`. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open Nacre Font
open BoreP Fief rates Braid Rel Souk
variable (L:Side)(K: Teller G₅)(P:Patch)(e η c u d α D:ℝ)(l j n k:ℕ)(q:Chi)
lemma payer_fValid (w:Odd L.val)(p:P.Branches K.bind SU.group)(W:∀ i:ℕ,3 ≤ i → i ≤ n+3 → Push.Uniform.Before G₅ K.top.width K.top.paths K.j K.bind i)(hx:1≤l)(hl:l≤18)(hp:3≤n)(h:l+78 ≤ j)(t:0<e)(hH:0<α)(hD:0≤D)(hu:0<η)(g:0≤u):∃ J:ℝ→ℝ,sizeK P.L 3 J∧∀ᶠ x:ℝ in atTop,∀{m X B:Side}(T:Roam m X B)(F:Tube G₅ T), (j+j+101)*radiusB x ≤ (More (CSide m B)).val→ Cert P K T F x→∀ Z:Monk SU.group T,sizedP SU.group P K T F Z.park → Z.key.flags=flags (temp x) Z.V →∀ {G:Ratio (CSide m B) (CSide X B)}, T.ratio=ratio G → Fleck G t Z.park η c n→∀ (A:Haze m X B G e) (V:Aim (CSide X B))(V':Aim (CSide m B))(H:Male), Ind G A α D c n (Budget L w V.den V'.den G H k)→ (∀ z,Critical Z.park F.high F.up z→ cFoot 3 (emergence L k w G Z.park z H V.den-flareP L k w H V'.den)) →‖Z.z‖ ≤ u*Scales.p G₅ P.L x →∀ β∈ Set.Icc (y G₅ P.L x/2) (2*y G₅ P.L x),∀(d:ℝ)(v: Directions G₅ (More (CSide m B))→Rent0 G e)(i j':Single (CSide m B)),place_x i∉ Z.key.dome (j*radiusB x)→ (∀ᶠ t' in 𝓝 0,Bride G F x d q l (Cay.rough (Z.atop t' x) 0) (v t') β (radiusB x+1) (place_x i))→ Allows n (fun y=> Corne.led G x A (v y) i j') 0 (J x):=by
 obtain ⟨a,B,v,R,S,M,Q,ha,hB,hR,hQ,hM,H⟩:= sting K P p n l (j-2) hp hl (W _ (by omega) (by omega)) (W _ (by omega) (by omega)) u g; let Z:= max D B; obtain ⟨W₀,X,Y,hW,hX,hY,ht⟩:= weather (C:=c) (b:=Z) K P p (W _ (by omega) (by omega)) hp t hH (hD.trans (le_max_left ..)) hu L w k l hx
 let J(x:ℝ):= (Cay.burn a x P); let V(x):=Corne.dataC n (Jet.composeCost n (Y*J x^3) (1/2)); have he:sizeK P.L 3 V:=(rates.arm _ _ _ (((burn_k ..).square 3).scale Y)).scale _
 refine ⟨V,he,?_⟩; filter_upwards [H, (burn_k P a).spine.eventually (ge_mem_nhds hW),ht] with x hZ hx hg m X₀ B' T F g' p Zm u hu G i he A V V' M' h' hk w β b d v i₁ i₂ t0 K0
 obtain ⟨y,y',h₁,x₁,v₁,S⟩:=hZ; obtain ⟨z,u₁⟩:= S _ b; obtain ⟨j₁,X',Y',a,b,g,R',p'⟩:= u₁ T F p Zm (place_x i₁) q ((Nat.mul_le_mul_right _ (by omega)).trans g') u hu (by rw [Nat.sub_add_cancel (show 2≤j by omega)]; exact t0) w
 have hI: Ind G A α Z c n (Hest.Budget L ‹Odd L.val› V.den V'.den G M' k):=by obtain ⟨W,v,H⟩:= h'.port; exact ⟨⟨W,v,H.book (le_max_left ..)⟩,h'.meet,h'.motion⟩
 -- WRONG hg P invoked b enlarged cost. ensure Z from explicit argument
 have hh(y':Mast G₅ _)(hv:‖y'‖<1):Slate.Fire F x Zm.park Zm.k l (J x) n Z y':=by
    let U:= Y' y' hv; refine { U.toSpice.more h₁.le (le_max_right ..) with flame:=fun q' d'=>?_}
    obtain ⟨p,v,i',j'⟩:=U.flame q' d'; refine ⟨p.mono (le_max_right ..),v.mono (le_max_right ..),i'.mono (mul_le_mul_of_nonneg_right (le_max_right ..) h₁.le), j'.mono (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg h₁.le _))⟩ -- definitional change protected
 let X₀:= hg.2 T F Zm.park p u he A V V' M' hI hk Zm.k _ y hx
 exact forkY G F x d (J x) q l Zm β t A i₁ i₂ i p.funds.1 j₁ v₁ g R' p' Y ⟨fun y t=>(X₀ y t).2.1,fun y t=>(X₀ y t).2.2⟩ hh v K0 (by omega) hI he
end YM.CF.Lor
