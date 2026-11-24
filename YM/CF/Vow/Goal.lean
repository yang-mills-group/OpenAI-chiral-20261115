import YM.CF.Vow.Move
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
variable {F G: Copy n}
lemma Medal.big (p:Medal P X D F h a)(u:a≤b):Medal P X D F h b:=by obtain ⟨t,v,h,f,g⟩:=p; exact ⟨t,v,h,f,g.trans u⟩
lemma Medal.wage (p:Medal P X D F h a)(t:0≤ h):0 ≤ a:=by obtain ⟨v,h,g,k⟩:= p.pays; exact (sum_nonneg fun i _=>mul_nonneg (pow_nonneg t _) (h i)).trans k
lemma Medal.zeroT : Medal P X D 0 h 0:=⟨⟨fun _ _ _ _=>rfl,fun _=>Flour.trivial,measurable_const,fun _ _=>(map_zero _).symm⟩, 0,le_rfl,fun _ _ _ _=>Woody.empty _,by simp [joinV]⟩ -- tune implicit
lemma Medal.oneT : Medal P X D 1 h 1:=by
 refine ⟨⟨fun _ _ _ _=>rfl,fun _=>Flour.grainE,measurable_const,fun _ _=>(map_one _).symm ⟩,Pi.single ∅ 1, Woody.p (E:=ℂ) (Woody.uniV (k:=1) 0),fun _ _ _ _=>Woody.uniV _,?_⟩; -- p type
 simp [joinV,Pi.single_apply,mul_ite,stake]
lemma Medal.plus (p:Medal P X D F h a)(q:Medal P X D G h b) : Medal P X D (F+G) h (a+b) :=by
 obtain ⟨Z,g,u,v,w⟩:=p; obtain ⟨W,q,k,l,m⟩:=q; exact ⟨⟨fun i j f g=> congrArg₂ (·+·) (Z.same i j f g) (W.same i j f g),fun i=>(Z.lit i).add (W.lit _),Z.keeps.add W.keeps,fun i j=> (congrArg₂ (·+·) (Z.gaugeX _ j) (W.gaugeX i j)).trans (map_add ..).symm⟩,g+q,add_nonneg u k,fun i f _ x=> (v i f x).addP (l i f x),by rw [joinVadd]; exact add_le_add w m⟩
lemma Medal.rum (p:Medal P X D F h a)(k:ℝ): Medal P X D (k • F) h (‖k‖ *a):=by
 obtain ⟨Z,b,v,g,u⟩:=p; refine ⟨⟨fun i j f g=> congrArg (k • ·) (Z.same i j f g),fun i=>(Z.lit i).rsmul k,Z.keeps.const_smul k,fun i j=> (congrArg (k • ·) (Z.gaugeX i j)).trans (map_smul ..).symm⟩,‖k‖ • b,fun i=> mul_nonneg (norm_nonneg _) (v i),fun i t _ q=> Rue.covering k (g i t q),?_⟩; unfold joinV; simp only [Pi.smul_apply, smul_eq_mul,mul_left_comm _ ‖k‖,← mul_sum]; exact mul_le_mul_of_nonneg_left u (norm_nonneg _)
lemma Medal.negT (p:Medal P X D F h a):Medal P X D (-F) h a:=by simpa using p.rum (-1)
lemma Medal.cross (p:Medal P X D F h a)(w: Medal P X D G h b)(s:0 ≤ h):Medal P X D (F*G) h (a*b):=by
 obtain ⟨t,k,u,x,z⟩:=p; obtain ⟨l,v,y,i,j⟩:=w; refine ⟨⟨fun o q g m=>congrArg₂ (·*·) (t.same _ q g m) (l.same o q g m),fun o=>(t.lit o).mul (l.lit o),t.keeps.mul l.keeps, fun o q=> (congrArg₂ (·*·) (t.gaugeX o q) (l.gaugeX o q)).trans (map_mul ..).symm⟩,skirt k v, skirtPos _ _ u y,fun i' g _ R=> (x i' g R).pairP (i i' g R),?_⟩
 exact (turnS (stokes s) k v u y).trans (mul_le_mul z j (sum_nonneg fun i _=>mul_nonneg (pow_nonneg s _) (y i)) ((sum_nonneg fun i _=> mul_nonneg (pow_nonneg s _) (u i)).trans z))
lemma Medal.sumP {I:Type*}(S: Finset I)(V:I → Copy n)(v:I→ℝ)(p:∀ i∈ S,Medal P X D (V i) h (v i)) : Medal P X D (∑ i∈S,V i) h (∑ i∈S,v i):=by induction S using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact zeroT| insert i S u ih=>rw [sum_insert u,sum_insert u]; exact (p i (mem_insert_self ..)).plus (ih fun i' a=>p i' (mem_insert_of_mem a))
lemma Medal.prodP {I:Type*}(S: Finset I)(V:I → Copy n)(v:I→ℝ)(p:∀ i∈ S,Medal P X D (V i) h (v i))(t:0≤h): Medal P X D (∏ i∈S,V i) h (∏ i∈S,v i):=by induction S using Finset.induction_on with| empty=> rw [prod_empty,prod_empty]; exact oneT| insert i S u ih=>rw [prod_insert u,prod_insert u]; exact (p i (mem_insert_self ..)).cross (ih fun i' a=>p i' (mem_insert_of_mem a)) t
lemma Medal.stretchB (p:Medal P X D F h a)(g:X ⊆ Y)(t:D⊆Z)(s:X\D⊆Y\Z): Medal P Y Z F h a:=by
 obtain ⟨V,k,i,l,m⟩:=p
 exact ⟨⟨fun o q u v=> V.same o q (agrees_mono u (Finset.coe_subset.mpr g)) fun j h=>v (g h),fun i=> (V.lit i).lift fun k u=>mem_filter.mpr ⟨mem_univ _,g (mem_filter.mp u).2⟩,V.keeps,V.gaugeX⟩,k,i,fun x u _ v=> l x (grow_b s u) (t.trans v),m⟩
open Rue
lemma Medal.expressT (p:Medal P X D F h a)(t:0 ≤h) : Medal P X D (fun u=> exp (F u)-1) h (Real.exp a*a):=by
 let W:= Cipher n; letI:NormedAlgebra ℚ W:= NormedAlgebra.restrictScalars ℚ ℝ W; obtain ⟨v,q,u,m,f⟩:=p
 refine ⟨⟨fun i j s t=> by rw [v.same i j s t], fun i=>?_, (exp_continuous (𝔸:=W)).measurable.comp v.keeps |>.sub measurable_const,fun i j=>?_⟩,saber q 1,(saber_r 1 u _ (stokes (X:=Dwell n) t)).1,fun i l _ x=>wiser (m i l x),?_⟩ -- tune syntax
 · let L:=stretch (camp X); apply (stretch_ok _).mp; refine L.sub_mem ?_ L.one_mem; exact exp_mem (R:=ℝ) (show IsClosed (L:Set W) from Submodule.closed_of_finiteDimensional L.toSubmodule) ((stretch_ok ..).mpr (v.lit i))
 · let U':= Scree.paintR false false (tradew n j); change exp _-_ = U' _; rw [v.gaugeX,map_sub,map_one]; rw [map_exp U' U'.toLinearMap.continuous_of_finiteDimensional]
 exact (peony 1 u (stokes t)).trans (by rw [pow_one]; exact mul_le_mul (Real.exp_monotone f) f (sum_nonneg fun i _=>mul_nonneg (pow_nonneg t _) (u i)) (Real.exp_pos _).le)
lemma Medal.capF (p:Medal P X D F h a)(t:1≤ h)(v:Orbit n)(q:pingS P.threshold (X\D) v.1): ‖F v‖ ≤ a:=by
 obtain ⟨w,c,e,g⟩:=p.pays; refine (Pastry.lies t _).trans (le_trans ?_ g); unfold Pastry.tier joinV; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans t) _)
 have ht := (e v q (Subset.refl _)).haveP i; have he:‖crumb (F v).val i‖ ≤ potash 1 P.order (SongF (fun y:tangD n=> (F (pressQ P D v.1 y,v.2)).val) i) 0:=by -- tune
    unfold potash; refine le_trans (le_of_eq ?_) (single_le_sum (f:=fun j=> noble 1 j (SongF (fun y:tangD n=> (F (pressQ P D v.1 y,v.2)).val) i) 0) (fun j _=>pos_nob zero_le_one j) (show 0 ∈ _ from mem_range.mpr (Nat.zero_lt_succ _))); simp [noble,SongF,pressQ,born]
 exact he.trans ht.earned
end YM.CF.Vow
