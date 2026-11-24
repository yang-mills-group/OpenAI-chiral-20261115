import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e m0 t z α b c A B':ℝ} {j k k' m n:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
local notation "C"=> W.C
local notation "κ"=> QuotaH V.f V.g V.F1 V.F2
local notation "Yw"=> arcB V.f V.g V.F1 V.F2
open Cascade
-- ledger.Static quotas at this script. Point β F,V & mast may contain independently outputs purchased AFTER weighted exp radius α. Permit conditional K. Need h chosen after $meters so Vista Vparam last$. Aims history used.
lemma ample_strict (k n:ℕ)(h:3 ≤ k)(p:CutZ A K.j n) : ∃ e:ℝ,0< e ∧ ∀{B:Side}{d:ℝ}(U:Grasp V.U B d)(W:GivenX V U),d≤e→ U.baseline ≤ O.d → ∃ Q:Isle,1<Q.fine ∧∃ m:ℕ,∀ {P N:Side}(G:Ratio (mid N B) (mid P B)),G.count=R.L→ m≤ (mid N B).val →∀ (M:Interest (mid P B))(L₀:Interest (mid N B)), InterestX W.C _ M→ InterestX W.C _ L₀→∃ D:Sheep V U W G M L₀ k n A, Sheet.isle D=Q:=by
 have hx:= V.L.lobby ▸ R.order_cut; obtain ⟨k2,hK2,H⟩:=rootWide (by omega : 1 ≤ k) R.L
 let K':=max k2 2; have h_:1<K':= lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_right ..); have hK:= h_.le
 have h₁:= V.pos1; have h₂:= V.pos2; have hw:=V.width1; have hg:=V.width2
 obtain ⟨c,g,F⟩:=cost_c h₁.le h₂.le hw hg V.d_o V.sp V.note (by omega) V.gate k K' hK
 obtain ⟨a₁,f,e₁,x₁,y,z,w,Z⟩:= bound_δ (Y:=V.U) R.L k K' hK h₁.le h₂.le hw hg (by omega) V.gate
 obtain ⟨a,u,e,x,i,j,N,B⟩:= gates p V.gate (by omega) hw hg h₁.le h₂.le R.L R.odd_side; obtain ⟨t,z₁,Q₁,q,m,Qw⟩:= auric k 2 (by norm_num) V.gate (by omega) h₁.le h₂.le hw hg V.note O
 let r':= min (min c e) (min t e₁); refine ⟨r',lt_min (lt_min g j) (lt_min z₁ z),fun {B₁ d} U W h' l=>?_⟩
 let T₀:=W.C; have hp:=W.health; obtain ⟨α',t1,Y,t2,S⟩:= Qw U W.pearl hp ((h'.trans (min_le_right ..)).trans (min_le_left ..)) l; have ha:= W.C.posb; have hC:= W.C.posB
 obtain ⟨c₂,T',x₂,t₃,P,F'⟩:=F U hp ((h'.trans (min_le_left ..)).trans (min_le_left ..)) W.pearl W.C.b W.C.B ha hC.le; obtain ⟨T,t',H'⟩:= H d hp; obtain ⟨R',b,hb,hd,D⟩:=cropsI (D:=Q₁) k ha (by linarith) hC -- tune
 let Q:Isle:=⟨T,c₂,T',a₁,f,Q₁,a,u,K',2,R',b,α',t1⟩
 let I:=N+U.roundZ+w+m+P; refine ⟨Q,h_,I,fun {P' N'} G ht hi L L' A A'=>?_⟩
 have hv:I ≤ (mid P' B₁).val:= hi.trans (by rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property)
 obtain ⟨hx,F₀⟩:= F' G ht ((show P ≤ I from by unfold I; omega).trans hi) L'.I L.I L.P L.M A'.leanJ.2 A.leanJ.2 A'.tilt A.tilt (tollX _ W A) A.ready; obtain ⟨F₂,H₂,S'⟩:=F₀ T
 obtain ⟨F₁,Q₂⟩:=Z U V.note W.pearl ((h'.trans (min_le_right ..)).trans (min_le_right ..)) hp G ht (by change I ≤ (CSide N' B₁).val at hi; unfold I at hi; omega) L'.P L.P L.M (tollX V W A') (tollX V W A) A.ready A'.ready hx -- tune
 obtain ⟨i',t,r⟩:=demand _ h₁.le h₂.le L.P (tollX V W A) L.M; have hh:Odd G.count.val:=ht.symm ▸ R.odd_side
 obtain ⟨U₁,U₂,Z⟩:= B V.note W.pearl hp ((h'.trans (min_le_left ..)).trans (min_le_right ..)) ht (by change I ≤ (CSide N' B₁).val at hi; unfold I at hi; omega) hh i' L.P t A.ready (by rw [r]; exact hx)
 have he(W':ℝ)(g:1 ≤ W'):= S (show max m U.roundZ≤(mid P' B₁).val from by unfold I at hv; omega) L.P L.M (tollX V W A) W' g
 obtain ⟨Vw,hW⟩:=D P' B₁ d L.I A.leanJ.2; obtain ⟨p,l,k'⟩:=he 1 le_rfl
 refine ⟨⟨hh,0,T,a,u,K', t',x,i,hK,fun F=> H' F G ht _ (le_max_left ..),F₁,a₁,f,x₁,y,Q₂,c₂,T',0,x₂,t₃,F₂,H₂,S',hx,i',U₁,U₂,Z,r,2,Q₁,(by norm_num),q,k',R',b,hb,hd,α',t1,Y,t2,Vw,hW,fun v g=>?_⟩,rfl⟩; obtain ⟨W,h,x'⟩:= he v g; exact ⟨W,h⟩
end YM.CF.Stake

namespace YM.CF.Stake
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
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z v g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y β:ℝ}(p:BudgetPoint){t₀ v v₁ p1 p2 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
variable {X: Interest (mid N B)}{Y:Interest (mid P B)}{U: Grasp V.U B d}{W:GivenX V U}
variable (M: Sheep V U W G Y X k n A)
local notation "sN"=>mid N B
local notation "θo"=> Hest.Budget R.L R.odd_side Y.P.den X.P.den G Y.M K.j
local notation "Δ"=> shipA G U Y.M Y.P.den Y.I X.I
local notation "TΦ"=> (Thera.yet_one)
variable (F: Pilot)(q:Chi){S' D':ℕ}
-- expose program β for ALL basis. Output C history ζ trial independent. avoid choices depend on post path.ClockB. Stencil projection sizes. Integrated maturity of Ls.
open Reef
variable (Z:Pluck R)(P₁ P₂:BudgetPoint)
-- Choose large constants compatible with grants, **BEFORE β**, all areas. even supplement later. l+100≤j.
set_option quotPrecheck false
set_option maxHeartbeats 1700000 in
lemma stakeWide (B:Side)(V:Grace K R L){U: Grasp V.U B d}(W:GivenX V U)(Q: LocalRatio L)(k l j:ℕ)(hp:6≤ k)(hx:5 ≤ l)(hv:l ≤18)(he:l+100 ≤ j)(F:Pilot)(HF:4*F.gear<L.radius)(I:Isle) (x':0<I.a)(s:0<I.s)(t:0≤I.pay) (q:Chi):∃ (Z:Pluck R),coastA j l+10 ≤ Z.r2 ∧ ∃ N:ℕ,∀ᶠ x in atTop, FireK L q F R K l k j x→∀ {m X:Side}{S:StepData (Domain m B) (Domain X B)}{T:Tube SU.group S}{G: Ratio (mid m B) (mid X B)}(γ α:ℝ),Punt V S T α x G → N*radiusB x ≤ (Domain m B).val →∀ (P₀: Interest (mid m B))(P₁: Interest (mid X B)), Mint U W.C γ K P₁ P₀ G S T.up T.down → ∀ {A:ℝ}{n:ℕ}(M:Sheep V U W G P₁ P₀ k n A),Sheet.isle M=I→∀ P' P'',∃ D:HeadL G S x d T P' P'',∀ β:ℝ,let X':= HeadL.turnR P' P'' D β; GiftP V X' M P' P'' F q α γ β l j ∧ MatP V X' M F Z:=by
 let Y:=R.L
 let poot : ℝ:= K.top.drift+ abs (SU.group.slopeConstant*Real.log R.L.val)
 have hR:0≤poot:=by unfold poot; have ht:=K.top.drift_ge; positivity
 obtain ⟨u,E,v,B',m,pU,P',pE,pv,pB',pM,X⟩:=lampZ K R k l V.L.cloth (by omega) (by omega) hv (before_t K _ (by omega)) (before_t K _ (by omega)) (before_t K _ (by omega)) q L Q _ V.W.bar V.W.peak V.W.rise poot F.toll HF V.W.large.le V.W.slow hR
 obtain ⟨t1,s1,f,g,M,e',b,p,qb,hf,hg,hM,H⟩:=sausage (C:=I.fine) (D:=U) (w:=W.C.P) K R (by omega : 3≤ k) V.L.cloth Q (by omega) hv F.toll HF W.C.posP.le t (before_t K _ (by omega)) (before_t K _ (by omega)) (before_t K _ (by omega)) q V.W.bar W.health s x'
 obtain ⟨Vx,Wx,E',X',v1,w1,u1,t',hV,hW,hE',hX',z,v',s',j',Q₀⟩:= sing_kValid j k l hx R K q hv (by omega) (by omega) V.L.cloth (fun i p _=> before_t K i p) -- hp' fix
 obtain ⟨J,HZ,V₁,W₁,T₁,T₂,F₁⟩:=roll_k R.L v B' u l j k E pE pv pB' (by omega) pU (by omega) -- order
 obtain ⟨J',q',V₂,W₂,R',W',F₂⟩:=roll_k R.L f g t1 l j k M hM hf hg (by omega) p (by omega)
 let r2:=2*(j+J+J'+v1+l+210); let r3:= 16*r2
 let Z:Pluck R:=⟨r3,r2,Vx,Wx,V₁,W₁,V₂,W₂,hV,hW,T₁,T₂,R',W',by unfold r3; omega⟩
 refine ⟨Z,by change coastA j l+10≤r2; unfold coastA coverB; omega, r3+1000,?_⟩; filter_upwards [X,H,Q₀,F₁,F₂, Corne.wants u pU k (l+76) (by omega), Corne.wants s1 qb k (l+76) (by omega)] with x h g f hU hu hJ hx
 let Y:=radiusB x; intro Fk N P S T G γ α P' Ih Px Py Wk A n Ls I' D D'; dsimp only at g hU hu f h -- tune
 let d' := F.skin R x; obtain ⟨K₁,K₂⟩:= hU; obtain ⟨p₁,p₂⟩:= hu; obtain ⟨kQ,tQ⟩:= f; have hx':J*Y*2 + J'*Y*2 + v1*Y*2 + (j+l+210)*Y*2=r2*Y:=by unfold r2; ring
 have h₁: E Y≤ J*Y:= K₁.trans (Nat.mul_le_mul_right _ (by omega)); have h₂:M Y≤ J'*Y:=p₁.trans (Nat.mul_le_mul_right _ (by omega)); have h₃:E' (Cay.horn x l) ≤ v1*Y:=kQ.trans (Nat.mul_le_mul_right _ (by omega)); have hT':1000≤ Y:=Fk.blade
 have ht' :r3*Y+1000*Y ≤ (More (mid N B)).val:=by rw [←Nat.add_mul]; exact Ih
 have hQ:r3*Y=16*(r2*Y):= by rw [←mul_assoc]
 have hj:J*Y+j*Y ≤ r2*Y:=by have hb:= Nat.mul_le_mul_right Y HZ; omega
 let C:=P'.cert; have ht:= Wk.fiscal; obtain ⟨uX,kX⟩:= h S T C P'.up P'.down α (by
    have hb:=P'.fee; unfold poot; generalize hf:SU.group.slopeConstant*Real.log (R.L.val)=e at hb ⊢; have hg:=abs_sub (α+e) e; rw [add_sub_cancel_right] at hg; linarith only [hb,hg]
 ) (fun t=>P'.sized _) (fun k z v=> (P'.matchP _ _ v).2) (by change Y≤(More (mid N B)).val; omega) (by change E Y<(More (mid N B)).val; omega)
 let U₀:= Ls.ink; let V_:=snowG G T q x s1 γ d' l Ls.ink W.health
 obtain ⟨A',vX⟩:= kX d'; obtain ⟨z',ho,hX,hp⟩:= shapeL _ _ I I'; -- tuning types
 obtain ⟨U',kL⟩:= g _ G T C P'.up P'.down P'.scaleP P'.rareH Ls.ink Py.P Px.I Py.I Py.M γ ht Ls.led (by rw [z',ho,hX,hp]; exact Ls.lake) (fun f=> ⟨P'.sized _,fun z p=>by rw [P'.height] at p; rw [P'.garden]; exact (Wk.hope f z p).2,by rw [ho,hp]; exact Ls.quota f⟩) (by change M Y < (More (mid N B)).val; omega)
 obtain ⟨FW,htq,hZ'⟩:= kL d'; obtain ⟨U'',H₀,W₀⟩:=tQ S T ⟨C,fun x=>⟨P'.sized _,fun z p=> (P'.matchP _ _ p).1⟩⟩ (by change (v1+_+_)*Y≤ (More (mid N B)).val; simp_rw [Nat.add_mul]; omega) d'
 -- head
 let Gk:Muster G S x d T:=⟨W.health,0,α,γ,d',l,j,D,D',q,L,u,s1,F.gear,U'',A',FW,v1,J,J',U₀,Ls.fame,⟨1,warm W.health.le⟩⟩ -- L shadow ChartRatio.VERT.
 let PA:HeadL G S x d T D D' :=⟨Gk⟩; refine ⟨PA,fun β=>?_⟩; intro P₀
 refine ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,?_⟩
 have hh:= (Fk.worn _ C).2.1; let R':= r2*Y; let m:= Cay.horn x l; have hv:J*Y+J*Y≤R':=by omega
 have hg:J'*Y+J'*Y≤R':=by omega
 have hw:v1*Y+v1*Y≤R':=by omega
 have hK:m≤R':=by unfold m Cay.horn; change (l+76)*Y≤_; simp_rw [Nat.add_mul] at hx' ⊢; omega
 constructor
 · rw [z',ho,hX,hp] at U'; exact ⟨_,_,U'⟩
 · intro M p; have hv':=(P'.sized M.park); have hq:(l+76+(l+76)+101)*Y ≤ (Domain N B).val:=by change _ ≤ (More (mid N B)).val; simp_rw [Nat.add_mul]; simp_rw [Nat.add_mul] at hx'; omega
   refine ⟨Corne.capAX _ _ _ _ _ (α+γ) l M β L F.gear j (uX _) C.funds.1 hh pM Fk.blade (by omega) ?_, fun i hi=>?_⟩ -- tune order
   · intro i hi; refine Corne.beatY _ _ _ (hJ S M p hq _ ?_) (by simp_rw [Nat.add_mul]; omega); exact fun t=> hi (farther (Nat.mul_le_mul_right _ (by omega)) t)
   · refine Corne.beatY _ _ _ (hx S M p hq _ ?_) ?_; exact fun t=> hi (farther (Nat.mul_le_mul_right _ (by change _ ≤ j; omega)) t); change Cay.horn x l ≤_; unfold Cay.horn; simp_rw [Nat.add_mul]; omega
 · exact ⟨_,_,_,_,_,_,_,_,_,_,_,_,H₀,vX,htq⟩
 · -- ledger
   have hp:Census P₀ R' ((l+90)*Y) (Z.N1*Y):=by
     have hV: Z.N1*Y =16*R':= hQ
     have hl:1 ≤ R':=by simp_rw [Nat.add_mul] at hx'; unfold R'; omega
     refine ⟨?_,?_,?_,?_,?_,?_,?_, ?_,?_,?_,?_,?_,?_⟩ -- tune change for line
     · change (l+100)*Y ≤ _; simp_rw [Nat.add_mul] at hx' ⊢; omega
     · change j*Y≤_; omega
     · change Y+1+(l+90)*Y ≤ r3*Y; simp_rw [Nat.add_mul]; simp_rw [Nat.add_mul] at hx'; omega
     · change coverB l j*Y≤ r3*Y; unfold coverB; simp_rw [Nat.add_mul,mul_assoc]; rw [Nat.add_mul]; simp_rw [Nat.add_mul] at hx'; omega
     · intro i P; change i∈ ({v1,J,J'}:Finset ℕ) at P; simp only [mem_insert, mem_singleton] at P; rcases P with Hs|Hs|Hs <;> subst i <;> change _*Y+_≤ _ <;> omega
     · change R'+1 ≤ r3*Y; omega
     · change R'+R'+1 ≤ r3*Y; omega
     · exact mint_u _ _ (orm _ _ _ H₀) (h₃.trans (by omega))
     · exact mint_u _ _ (ork _ _ _ vX) (h₁.trans (by omega))
     · exact mint_u _ _ (ork _ _ _ htq) (h₂.trans (by omega))
     · refine can_f _ _ H₀ _ (by omega) fun i j p h=> fameK hh Fk.blade (kind_m h (Corona.halo_mono hK (Subset.refl _))) -- tune
     · refine mild m _ (fun i t h2 x y u w=>?_ ) hK; refine Eq.trans (congrFun ?_ x) (((uX t).bonds d' h2).1.reads x y w); exact scopeR T _ _ _ _ _ _ _ _ _ _ u hh Fk.blade
     · refine mild m V_ (fun i t h2 x y u w=>?_ ) hK; refine Eq.trans (congrFun ?_ x) ((hZ' t h2).1.reads x y w); exact perk U' _ q _ _ _ u -- order tuning
   exact ⟨R',hp⟩
 intro i p j_ z' ht Q g t1; -- pace h/g/z intro
 have he: |0|≤(1:ℝ):=by norm_num
 obtain ⟨x',p'⟩:= W₀ β z' i p j_; obtain ⟨u',v'⟩:=K₂ S _ _ (by change (J+J+101)*Y ≤ (More (mid N B)).val; simp_rw [Nat.add_mul]; omega) vX _ (fun j=>(uX (i.park,i.k)).bonds _ j) i.key i.V p j_; obtain ⟨y,s⟩:=p₂ S _ _ (by change (J'+J'+101)*Y ≤ (More (mid N B)).val; simp_rw [Nat.add_mul]; omega) htq _ (hZ' (i.park,i.k)) i.key i.V p j_
 refine ⟨x',u',y,fun l=> ⟨p' (fun t=> l (farther ?_ t)), v' (fun t=>l (farther ?_ t)),s (fun t=>l (farther ?_ t))⟩⟩
 · change E' (Cay.horn x _)+v1*Y ≤ r2*Y; omega
 · change E Y+J*Y ≤ r2*Y; omega
 change M Y+J'*Y ≤ r2*Y; omega
end YM.CF.Stake
