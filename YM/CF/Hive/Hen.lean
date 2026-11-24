import YM.CF.Hive.Beam
import YM.CF.Levier.Ambo
import YM.CF.Hest.Boat
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
open Kennel Nacre Hest
lemma pier_z {P Q:Op n}(h:IsStarProjection P)(p:IsStarProjection Q)(q:sings b U P= swapX r Q)(X:Op n): lotB b r U (exp (dg (capT P X)))=exp (dg (capT Q (Thera.jazz r (sings b U X)))):=by
 have hp:Continuous (lotB b r U):= tour_c b r U
 letI : NormedAlgebra ℚ (FC n):=NormedAlgebra.restrictScalars ℚ ℂ (FC n)
 rw [map_exp _ hp]; congr 1; rw [← birth _ _ h]; change tourP U b r _ = _; rw [appleT h p b r U q,sailR,birth] -- check boot
open Laic
variable {N B L m:Side}{j:ℕ}{ho: Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}{P:Grasp Y B e}(K:Pearl P)(p:Stamped j L ho Y)(w:P.roundZ≤(CSide m B).val)(v:1≤j)
abbrev nest(P:Grasp Y B e)(I:Aim (CSide m B))(M:Male)(x:Skin m B):=acts (exp (dg (capT (spar j M x) (I.den x)))) (changeM P x M)
variable {a a' z l:ℝ} {M: Male}
include K p w v
lemma honey_x{U:Skin m B}(hp:Guard U e)(F:Site (Domain m B)→E): changeM P (gauge F U) M=effectK (tradew _ F).val (changeM P U M):=by
 let H:=P.couture w M; have he:=P.baseY.1; obtain ⟨i,g⟩:= Phase.cue_from U; unfold changeM; rw [phase_g P.topB he H U hp _ (starK P.topB he hp g) F (P.broadness _ w M),candle_cov U K p w v hp]; exact (map_smul (acts (quantU _).val) _ _).symm -- tune 
lemma birds (s:Shape)(U:UNI SpinIdx)(h:JetS s.s b (detX s.s) U)(X:Aim (CSide m B))(Z:X.toll a z l a')(k:Reef.Cry X)(t:Skin m B)(g:Guard t e):
 arum (siteU s b U _) b (detX s.s) (mateK _) (nest P X M t)=nest P X M (stir (xtra b) s t):=by
 let y:= stir (xtra b) s t; have hx:= keepC (xtra b) s _ e g; have ht:=P.broadness _ w M
 rw [nest,nest, arum_act,change_g K p w v t g M s b U h]; congr 2
 have hY: X.den (stir (xtra b) s t)=Thera.jazz (detX s.s) (sings b (siteU s b U _) (X.den t)):=by have hh:= prism_x b s X Z k t U h; rw [Moire.bloom_P,Moire.bloom_P] at hh; exact hh -- placeholders?
 rw [show X.den _= _ from hY]; apply pier_z _ _ _ (ht.projection _ g) (ht.projection _ hx); exact funde_f _ _ _ h _ _ v _ _ (p.fields_one _ (P.needed.trans w)) (g.shrink P.gem)
lemma salt_g(f:Site (More (CSide m B))→ E)(X:Aim (CSide m B))(Z:X.toll a z l a')(t:Skin m B)(hk:Guard t e): effectK (tradew _ f).val (nest P X M t)=nest P X M (gauge f t):=by
 let v':= tradew _ f; let W:=P.broadness _ w M; rw [nest,nest,honey_x K p w v hk]; let V:=gauge f t
 have hh:= Fock.swivel (quantU v'); -- tune lemma acts
 let x:=changeM P t M; let L:= exp (dg (capT (spar j M t) (X.den t)))
 change acts (quantU v').val (acts L x)=acts _ (acts (quantU v').val x); rw [hh]; congr 2 -- tune
 have hv:= (Pec.den_r Z).ripe t f; rw [hv]; exact pier_z false false v' (W.projection _ hk) (W.projection _ (hk.cov f)) (W.covary _ f hk).symm (X.den t)
end YM.CF.Hive
