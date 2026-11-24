import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Heliac
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
variable {p:BudgetPoint} (o:Skye.Seat n)
open TableF.Lenten.Loden Haro Tap Hove Moto
attribute [local instance] opCStarAlgebra
open Dial Nacre Ember Fir Fock
open Work.F03 Taxi TableF Bank HushP ModuleB Flot RG Hake
open Layout Fren
local instance(I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance(I:Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
abbrev Frac {n:Side}(T:marker0 n)(f:trans1 n)(z:ℂ)(g:marker0 n):ℂ:=UnEcho g T f/z
abbrev KnotU (F:Torches n)(o:Seat n)(g:trans1 n)(z:ℂ):Prop:=∀ S:marker0 n,Distant o S → Frac S g z (Ion F)=0
structure OrientL (G:trans1 n)(z:ℂ):Prop where
 receipt:Envelope G
 agency(w: Sweep n)(T: Torches n)(S: marker0 n)(o:Seat n):Distant (sh w o) S→ Envelope (Ion T)→Envelope (Ion (tiro w T))→ Frac S G z (Ion (tiro w T))=payZ w (Frac (SkiM w S) G z (Ion T))
-- flags.B assembly. W global.
structure Portage (F: Torches n)(o:Seat n)(p:BudgetPoint)(b a:ℝ)(V:Waves)(M:Male)(c d:ℝ):Prop where
 fare:Inscribe p o b a F c d
 legal:LegTax F
 port:MetaB o M V (AlphaY F.1) p b
 post:lifeH (AlphaY F.1) 1=0
variable {F H:Torches n}{W Z:Waves}{M:Male}{T:trans1 n}{b h v a c d' d c':ℝ}{z:ℂ}{o}
lemma say_P (F H:Torches n):Ion (F+H)=Ion F+Ion H:=by funext i; simp only [optics_T,Prod.fst_add,Prod.snd_add, Pi.add_apply,conn_a,Finset.sum_add_distrib]; abel
lemma say_s(F:Torches n)(v:ℂ):Ion (v • F)=v • Ion F:=by
 funext i; simp only [optics_T,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,conn_h,← Finset.smul_sum]; simp only [smul_add] -- tune
lemma KnotP (g:Envelope T)(u:KnotU F o T z)(e:KnotU H o T z)(t: Envelope (Ion F))(x: Envelope (Ion H)): KnotU (F+H) o T z:=by
 intro S p; have h0:=u S p; have h1:=e S p; rw [say_P]; unfold Frac UnEcho at *
 let f(X: marker0 n):Pane n→ℂ:= fun i=> letterRead (S i*X i) (T i); let Y:=Ion F; let Z:=Ion H; have he: (∫ i:Pane n, f (Y+Z) i ∂prior SU.group (More n))=(∫ i:Pane n,f Y i∂prior SU.group (More n))+(∫ i:Pane n,f Z i∂prior SU.group (More n)):= by
    have hh(i):f (Y+Z) i=f Y i+f Z i:=by change BookP S i T (Y i+ Z i)=_; rw [map_add]; rfl -- maybe rfl
    simp_rw [hh]; exact integral_add (Env.integrableX (env_letterRead (env_mult p.1 t) g) _) (Env.integrableX (env_letterRead (env_mult p.1 x) g) _)
 change (∫ i:Pane n, f (Y+Z) i ∂prior SU.group (More n))/z=0; rw [he,add_div]; change (_/z)+(_/z)=0; rw [show (_:ℂ)/z=0 from h0,show (∫ i:Pane n,f Z i∂prior SU.group (More n))/z=0 from h1,add_zero] -- ambiguity
lemma KnotZ (u:KnotU F o T z)(j:ℂ): KnotU (j • F) o T z:=by
 intro S p; let U:=Ion F; let Y(U:marker0 n)(i:Pane n):=BookP S i T (U i); rw [say_s]; change (∫ i:Pane n,Y (j • U) i ∂prior SU.group (More n))/z=0; have h(i):Y (j • U) i=j* Y U i:= (BookP S i T).map_smul j _; simp_rw [h]; rw [integral_const_mul,mul_div_assoc, show (∫ i:Pane n,Y U i∂prior SU.group (More n))/z=0 from u S p,mul_zero]
lemma Fare_R (u:Portage F o p h a W M c d) (l:c≤c')(t:d≤d')(v:b≤a): Portage F o p h b W M c' d':=⟨⟨track_p u.fare.1 l,trace_p u.fare.2 v t⟩,u.legal,u.port,u.post⟩
lemma Fence (r:p.order≤6)(n:p.power≤3)(s:0≤h)(u:Portage F o p h a W M c d)(v:Portage H o p h a Z M c' d'): Portage (F+H) o p h a (W+Z) M (c+c') (d+d'):=by
 let B:=(F+H).1; have hx:AlphaY B= AlphaY F.1+AlphaY H.1:=Alpha_add ..; refine ⟨⟨track_a u.fare.1 v.fare.1,trace_u u.fare.2 v.fare.2⟩,⟨port_add u.legal.1 v.legal.1,fun i=>port_add (u.legal.2 i) (v.legal.2 i)⟩,hx.symm ▸ (linearHU _ _ u.port v.port s (sprig o u.fare.1 n r u.legal.1) (sprig o v.fare.1 n r v.legal.1)),?_⟩
 rw [show AlphaY _=_ from hx,life_add, Pi.add_apply,u.post,v.post, zero_add]
lemma Foam (r:p.order≤6)(n:p.power≤3)(s:0≤h)(u:Portage F o p h a W M c d)(j:ℂ): Portage (j • F) o p h a (j • W) M (‖j‖*c) (‖j‖*d):=by
 have hx:AlphaY (j • F).1=j • AlphaY F.1:=Alpha_s ..; refine ⟨⟨track_h u.fare.1 j,trace_m u.fare.2 j⟩, ⟨port_m u.legal.1 j,fun i=>port_m (u.legal.2 i) j⟩, hx.symm ▸ linearHE _ _ u.port (sprig o u.fare.1 n r u.legal.1) j s,?_⟩
 rw [hx,life_smul,Pi.smul_apply,u.post, smul_zero]
lemma pay_i(T:Sweep n): payZ T 0=0:=by simp [payZ,cSignX]
lemma Fly(r: Sweep n)(u:Portage F o p h a W M c d)(t:p.order≤6)(x:p.power≤3)(s:0≤h)(w:300<n.val): Portage (tiro r F) (sh r o) p h a (Mason r W) M (CaseL*c) (CaseL*d):=by
 let H:=tiro r F; let V:=AlphaY H.1; have he:=tiro_fee r F u.fare; have hp:=citizen_port r F u.legal; have hx: Turns r (AlphaY F.1) V:= axis_V ..
 refine ⟨he,hp, fℓies _ _ _ (sprig o u.fare.1 x t u.legal.1) ((move_Φ r o).symm ▸ sprig (sh r o) he.1 x t hp.1) hx s W u.port (lt_trans (by norm_num) w) (Window_z _ w),?_⟩
 have ht:=hx.turns 1; rw [Facet.glacial] at ht
 change Pastry.pane (V 1)=_; rw [ht,HoldS]; change cast_B _ (lifeH _ _) =_; rw [u.post,map_zero]
lemma revel (r:Sweep n)(u:KnotU F o T z)(v:Portage F o p h a W M c d)(q:OrientL T z):KnotU (tiro r F) (sh r o) T z:=by intro S p; rw [q.agency r F S o p (Ion_env v.fare) (Ion_env (tiro_fee r _ v.fare)), u _ (Ski_D r S p),pay_i]
abbrev Earner (p:BudgetPoint)(G:trans1 n)(z:ℂ)(M:Male)(o:Seat n)(a h:ℝ)(F:Torches n)(P:Waves)(c d:ℝ):Prop:= Portage F o p h a P M c d∧ KnotU F o G z
-- u conditions!
lemma Blank_z : Portage (0:Torches n) o p h a 0 M 0 0:=by
 refine ⟨⟨track_zero,trace_Z⟩,⟨port_Z,fun i=>port_Z⟩,?_,?_⟩
 · change MetaB _ _ _ (AlphaY (0:Paper n)) _ _; rw [AlphaØ,show (0:InkD n)=_ from (show (0:InkD n)=fun _=> hollow 0 from funext fun i=> Subtype.ext (show 0=(0:ℂ) • (1:FC _) from (zero_smul ℂ _).symm))]; apply linearØ
 change lifeH (AlphaY (0:Paper n)) _=_; rw [AlphaØ]; rfl
lemma Blank_t: KnotU (0:Torches n) o T z:=by
 intro S p; have hp(i:Pane n): Ion (0:Torches n) i=0:=by rw [optics_T]; change marketD 0 i+ ∑ j:Hubber n, marketD 0 i=_; rw [conn_Z]; simp
 unfold Frac UnEcho; simp_rw [hp,mul_zero]; have he(i:Pane n): letterRead 0 (T i)=0:=(by unfold letterRead; change inner ℂ (mateK _) (acts 0 (T i))=_; rw [act_zero,inner_zero_right]); simp_rw [he]; simp
lemma PH_tile (b:Bool)(Y:PalOne)(P:Oneκ b Y)(t: Envelope T) (w:0<h)(g:20<n.val)(e:p.order≤6)(u:p.power≤3): ∃ V:Torches n, V.2=0 ∧ ∃ W:Waves, PH15 b W Y ∧ Earner p T z M o a h V W (Tolω*CostOle Y) 0:=by
 obtain ⟨q,hx,hU,y,K,tL,H,S⟩:=shinePH o b Y P w g u e M; let A:=Pyl b o (excels o Y) h; let Q:=sprig o q u e hx; let V:=exportM o M Q w.le rfl; have hp:MetaB o M V (AlphaY A) p h:= export_full o M Q w.le rfl; let F:Torches n:=(A,0); refine ⟨F,rfl,V, plainΦ M b Y P w g u e V hp, ⟨⟨q,trace_Z⟩, ⟨hx,fun i=>port_Z⟩,hp,tL ▸ rfl⟩,?_⟩ -- tune
 rintro X ⟨t0,D,l,q,Dv⟩; have he(i:Pane n): letterRead (X i*Ion F i) (T i)=0:=by
    have hh:Ion F=marketD A:=by unfold Ion; rw [show (∑ i:Hubber n,F.2 i)=0 from sum_eq_zero fun x _=>rfl,conn_Z, add_zero]
    rw [hh]; exact S i (T i) (X i) D l (Dv i)
 unfold Frac UnEcho; simp_rw [he]; simp
lemma G_tile(q:Clip)(x:ℝ)(l:Axis)(f:PlaqAxes)(e:F.1=isolate none (Gval o f p q x l))(u:Inscribe p o h a F c d)(v:LegTax F)(Z:x≠0)(A: KnotU F o T z)(w:0≤h)(t:10 < (More n).val)(hP:p.order≤6)(hY:p.power ≤3): ∃ W, E15 l f W ∧ Earner p T z M o a h F W c d:=by
 have hx:= sprig o u.1 hY hP v.1; let W:= exportM o M hx w rfl; have hp:=export_full o M hx w rfl; change MetaB o M W _ p h at hp; obtain ⟨ht,s⟩:= gauge_Shift M W x q f l (show MetaB o M W (AlphaY _) p h from (by rw [show Silex _=F.1 from e.symm]; exact hp)) Z t; refine ⟨W,ht, ⟨u,v,hp,?_⟩,A⟩; rw [e]; exact s
lemma Every_T(W: Waves)(w:0<h)(s:20<n.val)(d:p.order≤6)(e:p.power ≤3):∃ F: Torches n,F.2=0∧ Portage F o p h a W M (bushRate*‖W‖) 0:=by
 obtain ⟨X,v,l,c⟩:= banksP (o:=o) M W s w e d; let F:Torches n:=(X,0); refine ⟨F,rfl, ⟨v,trace_Z⟩,⟨l,fun i=>port_Z⟩,?_ ,?_⟩
 · rw [show AlphaY F.1= _ from c]; exact brace_M o M w W e d s
 rw [show AlphaY F.1=_ from c]; exact skin_C ..
-- linear closures
lemma tile_B {I:Type*}(s:Finset I)(X:I→ Torches n)(W:I→ Waves)(C' D:I→ℝ)(P:∀ i∈s,Portage (X i) o p h a (W i) M (C' i) (D i))(u:p.power≤3)(v:p.order≤6)(w:0≤ h): Portage (∑ i∈s,X i) o p h a (∑ i∈s,W i) M (∑ i∈s,C' i) (∑ i∈s,D i):=by induction s using Finset.induction_on with|empty=> simp only [sum_empty]; exact Blank_z|@insert i s e ih=> simp_rw [sum_insert e]; exact Fence v u w (P i (mem_insert_self ..)) (ih fun i t=> P i (mem_insert_of_mem t))
lemma Ear_flow {I:Type*}(s:Finset I)(X:I→ Torches n)(W:I→ Waves)(C' D:I→ℝ)(P:∀ i∈s,Earner p T z M o a h (X i) (W i) (C' i) (D i))(e:Envelope T)(u:p.power ≤3)(v:p.order≤6)(w:0≤h): Earner p T z M o a h (∑ i∈s,X i) (∑ i∈s,W i) (∑ i∈s,C' i) (∑ i∈s,D i):=by
 induction s using Finset.induction_on with|empty=>simp only [sum_empty]; exact ⟨Blank_z,Blank_t⟩| @insert i s p ih=>have hx:= ih fun i t=>P i (mem_insert_of_mem t); have ht:= P i (mem_insert_self ..); simp_rw [sum_insert p]; exact ⟨Fence v u w ht.1 hx.1,KnotP e ht.2 hx.2 (Ion_env ht.1.fare) (Ion_env hx.1.fare)⟩
-- climate.V resolution enough for PH orientations; derived Carm.Euclidean.Test.Vector SpanRes
structure Sundial (n:Side)(p:BudgetPoint)(G:trans1 n)(z:ℂ)(M:Male)(a h c d:ℝ):Prop where
 sideK : 300 < n.val
 poles : p.order≤6
 pact:p.power≤3
 high:0<h
 good:OrientL G z
 life:∀ o:Seat n,∀ l:Axis,∀ f:PlaqAxes,∃ F:Torches n,∃ W:Waves,E15 l f W ∧ Earner p G z M o a h F W c d
def Looms (x:Waves): Prop:= (∃ l f, E15 l f x)∨∃ (b:Bool)(Y:PalOne), Oneκ b Y∧ PH15 b x Y
def Advects (x:Waves):Prop:=∃ (n:Side)(r:Sweep n)(W:Waves), Looms W∧ x=Mason r W
def Resonance:=Submodule.span ℂ {W: Waves|Advects W}
lemma notedA(b:Bool)(Y:PalOne)(W:Waves)(U:Oneκ b Y)(v:PH15 b W Y): W∈Resonance:= Submodule.subset_span (show Advects W from ⟨1,1,W,Or.inr ⟨b,Y,U,v⟩,(lands_o ..).symm⟩)
lemma notedB(l:Axis)(f:PlaqAxes)(W:Waves)(v:E15 l f W): W∈ Resonance:= Submodule.subset_span (show Advects W from ⟨1,1,W,Or.inl ⟨l,f,v⟩,(lands_o ..).symm⟩)
lemma resonate(r:Sweep n)(W:Waves)(u:W∈Resonance): Mason r W ∈ Resonance:=by
 apply Submodule.span_induction (p:=fun x _=> Mason r x∈ Resonance) ?_ ?_ ?_ ?_ u
 · rintro x ⟨k,s,W,v,h⟩; rw [h]; let R:Sweep n:=⟨s.s,0,s.charge⟩; rw [show Mason s W=Mason R W from rfl,lands_t]; exact Submodule.subset_span (show Advects _ from ⟨n,R*r,W,v,rfl⟩)
 · have hp: Mason r 0=payZ r 0 • (Mason r W):=by rw [←payY_a]; rw [show (0:ℂ) • W=0 from (show ∀ {E : Type}[AddCommMonoid E][Module ℂ E](W:E), (0:ℂ) • W=0 from fun {_} _ _ W=> zero_smul ℂ W) W]
   rw [hp,pay_i, show (0:ℂ) • Mason r W=0 from (show ∀ {E : Type}[AddCommMonoid E][Module ℂ E](W:E), (0:ℂ) • W=0 from fun {_} _ _ W=> zero_smul ℂ W) _]; exact Resonance.zero_mem
 · intro x y _ _ e f; rw [show Mason r (x+y)= Mason r x+ Mason r y from sheen_plus ..]; exact Resonance.add_mem e f
 intro a x _ f; rw [payY_a]; exact Resonance.smul_mem _ f
lemma recoil(V:Waves)(u:V∈ Resonance):∃ C:ℝ,0≤C ∧∀ {n:Side}{p:BudgetPoint}{G:trans1 n}{z:ℂ}{M:Male}{a h c d:ℝ}, Sundial n p G z M a h c d→0≤ c → 0≤ d →∀ o:Seat n,∃ F:Torches n, Earner p G z M o a h F V (C*(c+1)) (C*d):=by
 apply Submodule.span_induction (p:=fun V _=> ∃ C:ℝ,0≤C ∧∀ {n:Side}{p:BudgetPoint}{G:trans1 n}{z:ℂ}{M:Male}{a h c d:ℝ}, Sundial n p G z M a h c d→0≤ c → 0≤ d →∀ o:Seat n,∃ F:Torches n, Earner p G z M o a h F V (C*(c+1)) (C*d)) ?_ ?_ ?_ ?_ u
 · rintro x ⟨k,s,V,w,g⟩; suffices h: ∃ C:ℝ,0≤C ∧∀ {n:Side}{p:BudgetPoint}{G:trans1 n}{z:ℂ}{M:Male}{a h c d:ℝ}, Sundial n p G z M a h c d→0≤ c → 0≤ d →∀ o:Seat n,∃ F:Torches n, Earner p G z M o a h F V (C*(c+1)) (C*d) by
      obtain ⟨C',v,H⟩:=h; refine ⟨CaseL*C',mul_nonneg (Nat.cast_nonneg _) v,@fun n P G z M a h c d u hC hD o=>?_⟩; let r:Sweep n:= ⟨s.s,0,s.charge⟩; let X:=sh r⁻¹ o; obtain ⟨F,t,w⟩:=H u hC hD X; have hp:sh r X=o:=azBack r o; refine ⟨tiro r F,?_, hp ▸ revel r w t u.good⟩; rw [g,show Mason s V=Mason r V from rfl, mul_assoc,mul_assoc, ← (show sh r X=o from hp)]; exact Fly r t u.poles u.pact u.high.le u.sideK
   rcases w with ⟨l,f,u⟩|⟨b,Y,v,y⟩
   · refine ⟨1,zero_le_one, @fun n P G z M a h c d t hC hD o=>?_⟩; obtain ⟨F,W,p,u',v⟩:= t.life o l f; rw [one_mul,one_mul,vital u p]; exact ⟨F,Fare_R u' (le_add_of_nonneg_right zero_le_one) le_rfl le_rfl,v⟩
   let C':= Tolω * CostOle Y; refine ⟨|C'|,abs_nonneg _, @fun n P G z M a h c d t hC hD o=>?_⟩; obtain ⟨F,f,W,A,B',D⟩:= PH_tile (o:=o) (M:=M) (z:=z) (a:=a) b Y v t.good.receipt t.high (lt_trans (by norm_num) t.sideK) t.poles t.pact; rw [skis b Y V W y A]; exact ⟨F,Fare_R B' ((le_abs_self C').trans (le_mul_of_one_le_right (abs_nonneg _) (le_add_of_nonneg_left hC))) (mul_nonneg (abs_nonneg _) hD) le_rfl,D⟩
 · exact ⟨0,le_rfl, @fun n P G z M a h c d t hC hD o=> ⟨0,Fare_R Blank_z ((zero_mul _).symm.le) ((zero_mul _).symm.le) le_rfl,Blank_t⟩⟩
 · rintro x y _ _ ⟨c,r,p⟩ ⟨v,h,q⟩; refine ⟨c+v,add_nonneg r h, @fun n P G z M a h0 u τ E hC hD o=>?_⟩; obtain ⟨F,p,v'⟩:=p E hC hD o; obtain ⟨L,r,q⟩:=q E hC hD o; rw [add_mul c v (u+1),add_mul c v τ]; exact ⟨F+L,Fence E.poles E.pact E.high.le p r, KnotP E.good.receipt v' q (Ion_env p.fare) (Ion_env r.fare)⟩
 rintro w x _ ⟨c,h,q⟩; refine ⟨‖w‖*c,mul_nonneg (norm_nonneg _) h, @fun n P G z M a h0 u τ E hC hD o=>?_⟩; obtain ⟨F,v,g⟩:=q E hC hD o; rw [mul_assoc ‖w‖ c _,mul_assoc ‖w‖ c _]; exact ⟨w • F,Foam E.poles E.pact E.high.le v w,KnotZ g w⟩

end MastTin
end YM.CF.XGarden
end
