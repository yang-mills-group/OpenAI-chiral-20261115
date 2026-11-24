import YM.CF.Buffered.Postmen
/-!
# Repetition: align the actual water and Paint and Cue

Inputs to ember made on the payer; show these aspects are automatic under
cover replication, even for non-payer input. Need no external projects for this.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Mail.Colony
open Function NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Wilson
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m B N v X P L:Side}
section small
variable (A:Planck N P L)
local notation "p₀"=> (slump A)
lemma glow_add (x y:Site N): Lattice.lift ((slump A).cut x - (p₀).cut y) = lift ((slump A).cut (x-y)):= by rw [too,too,too,map_sub]
lemma lift_down (x y:Site N)(p:2*separation x y < P.val): lift ((p₀).cut x-(p₀).cut y)=lift (x-y):=by
 rw [glow_add, lift_eq_iff]; constructor
 · nth_rw 1 [←wrap_lift (x-y)]; exact Macrame.branch ..
 intro i; have he:=component_le (x-y) i; unfold separation at p; omega
abbrev ladder (A:Planck N P L)(x:Site N)(z:Site P) := x+wrap N (lift (z-(slump A).cut x))
lemma rises (x:Site N)(y:Site P): (slump A).cut (ladder A x y)=y:=by unfold ladder; rw [Macrame.Window.port,wrap_lift,add_sub_cancel]
lemma right_lift (x:Site N)(y:Site P): lift (ladder A x y-x)=lift (y-(p₀).cut x):=by
 unfold ladder; rw [add_sub_cancel_left]; apply lift_eq_iff.2; refine ⟨rfl,fun i=>?_⟩; have he:= lift_centers (y-(p₀).cut x) i; have hx:= Mail.width A; omega
lemma climbs (x:Site N)(y:Site P) : separation (ladder A x y) x= separation y ((p₀).cut x):=by unfold separation pdist; simp_rw [right_lift]
lemma steps_back (x y: Site N)(p:2*separation x y<P.val): ladder A y ((p₀).cut x)=x := by unfold ladder; rw [lift_down A x y p, wrap_lift,add_sub_cancel]
lemma delta_near (x y:Site N)(p:2*separation x y<P.val)(i:Axis): delta1 P ((p₀).cut x i) ((p₀).cut y i)= delta1 N (x i) (y i):=congrArg (fun x:Cover=> (x i).natAbs) (lift_down A x y p)
lemma budget_eq (x y:Site N)(p:2*separation x y<P.val)(i:Axis): ((p₀).cut x i=(p₀).cut y i)↔ x i=y i := by
 rw [show ((p₀).cut x i=(p₀).cut y i ↔ delta1 P ((p₀).cut x i) ((p₀).cut y i) = 0) from ⟨fun h=>h ▸ d_id ..,d_equal _ _⟩, delta_near (p:=p)]; exact ⟨d_equal _ _,fun h=>h ▸ d_id ..⟩
end small
variable (A:Planck N v P)(B)
abbrev pulse (A:Planck N v P):= slump (forG N v A)
local notation "r"=> pulse A
local notation "t"=> slump (gauge_plan (SugarGrid A B))
lemma odd_foot (i:Axis)(u:Index N): OddAxis N (u i) ↔ OddAxis v ((r).cut u i):=by
 obtain ⟨u,rfl⟩: ∃ U:Cover,wrap (GridN N) U=u:=⟨natural u,Rush.nat_true u⟩; rw [show (pulse A).cut _=wrap _ u from Macrame.branch ..]
 have he (v:Side): OddAxis v (wrap (GridN v) u i) ↔ wrap (2:Side) u i=1:=by
    change (assembly (More v)).residue (wrap (GridN v) u) i=1 ↔_; rw [Ratio.residue_wrap]; rfl
 rw [he,he]
lemma fits_pass (u w:Index N)(v':2*separation u w< (GridN v).val): Fits N u w ↔ Fits v ((r).cut u) ((r).cut w):=by
 unfold Fits; apply forall_congr'; intro i; rw [show (r).cut u i=(r).cut w i ↔ _ from budget_eq (forG N v A) u w v' i,odd_foot A i u,odd_foot A i w,delta_near (forG N v A) w u (by rwa [separation_comm]) i] -- tune rw
lemma add_down (u:Index N): (slump (gauge_plan (SugarGrid A B))).cut (address N B u)= address v B ((r).cut u):=by
 nth_rw 1 2 [←wrap_lift u]; unfold Cube.address; simp_rw [Ratio.root_embed, Ratio.embed_wrap]; rw [show (slump _).cut _=wrap (Domain v B) _ from (Macrame.branch .. : _), show (r).cut _=wrap (GridN v) (lift u) from Macrame.branch .., Ratio.embed_wrap]; rfl
lemma scatter (z:Site (Domain N B))(q: Coin B): (pulse A).cut (Cube.selected N B z q)=Cube.selected v B ((slump (gauge_plan (SugarGrid A B))).cut z) q:=by
 let b:=Cube.selected N B z q; let x:= address N B b; have he:= picked N B z q; have ht:separation z x ≤ B.val:= (node_dist (select_mem N B z q)).le
 apply picked_iff.mp; intro i; unfold elect; change delta1 _ ((t).cut z i) _≤_
 rw [←(show address v B ((r).cut b) i=high v B ((r).cut b i) from high_here ..),← add_down (A:=A),delta_near (gauge_plan (SugarGrid A B)) z x (p:=by have hv:=enough v B; have hp:0<B.val:= B.property; exact (Nat.mul_le_mul_left 2 ht).trans_lt (show 2*B.val<(Domain v B).val from by omega)),radius]; have hv:=he i; unfold elect Cube.radius at hv; rw [←high_here (x:=b)] at hv; simp_rw [odd_foot (A:=A)] at hv; exact hv
lemma march_eq (V W:Site (Domain N B))(h:separation W V ≤ B.val)(o:Lattice.Order): march V W o=march ((t).cut V) ((t).cut W) o:=by unfold march; rw [lift_down (p:=by have hx:=enough v B; have hp:0<B.val:= B.property; exact (Nat.mul_le_mul_left 2 h).trans_lt (show 2*B.val<(Domain v B).val from by omega))]
lemma freight_eq (U :Skin v B)(z:Site (Domain N B))(q:Coin B)(i:Ballot):
 freight N B ((t).links U) z (Cube.selected N B z q) i= freight v B U ((t).cut z) ((r).cut (Cube.selected N B z q)) i:=by
 unfold freight; refine congrArg _ (sum_congr rfl ?_); intro o _; apply congrArg (fun x:E=>turn x i.val); unfold Cube.tax; rw [←add_down (A:=A), Macrame.Window.traveller,← march_eq B A _ _ ?_]; exact ((separation_comm _ _).trans_lt (node_dist (select_mem N B z q))).le
abbrev pullS (A:Planck N v P)(x:Cue v): Cue N := x ∘ (pulse A).cut
lemma painted (V :Skin v B)(i:Cue v) (w:Sq) (z:Site (Domain N B)) : paintV N B ((t).links V) (slot N (pullS A i)) w z= paintV v B V (slot v i) w ((t).cut z) :=by
 have he(m:Side)(U:Skin m B)(u:Cue m)(z:Site (Domain m B)) : Cube.paint m B U (slot m u) w z= ∑ j:Row, ∑ b:Coin B, score B b w j • freight m B U z (Cube.selected m B z b) (u (Cube.selected m B z b)):=by
    unfold Cube.paint; rw [Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro i _; unfold cash; simp_rw [ticks, sum_filter,sum_smul,picked_iff]; rw [sum_comm]; apply sum_congr rfl; intro q _; simp_rw [ite_smul,zero_smul]; rw [sum_ite_eq']; simp; rfl -- tune
 unfold paintV; rw [he,he]; refine congrArg Cube.ren (sum_congr rfl fun j _=>sum_congr rfl fun b _=>?_); rw [freight_eq,←scatter B A]; rfl
-- Stats transform
abbrev spot (A:Planck N v P)(x: Spot N) : Spot v:= Prod.map (pulse A).cut id x
abbrev past (A:Planck N v P): Ramp N→ Ramp v:= Prod.map (spot A) id
lemma budget2 : 2*1 < (GridN v).val:= by have he:= grid_has v; omega
lemma prev_v (u w: Spot N) (p:2*separation u.1 w.1<(GridN v).val) : Prev N u w ↔ Prev v (spot A u) (spot A w):=by
 have hx: spot A u=spot A w ↔ u=w:=by
    constructor; intro h; apply Prod.ext; swap; · change (spot A u).2=(spot A w).2; exact congrArg Prod.snd h
    have hu:∀ i, (r).cut u.1 i=(r).cut w.1 i:=congrFun (congrArg Prod.fst h); exact funext fun i=> (budget_eq _ u.1 w.1 p i).1 (hu i)
    exact fun h=> h ▸ rfl
 unfold Prev; exact and_congr (fits_pass A u.1 w.1 p) (and_congr Iff.rfl (Iff.not hx.symm))
lemma marches (u: Spot N)(L:List (Ramp N))(h:Moves N u L): Moves v (spot A u) (L.map (past A)):=by
 induction L generalizing u with
 | nil=> trivial
 | cons l L ih=>
   have ht:Prev N l.1 u:= h.1; refine ⟨(prev_v A l.1 u ?_).1 ht,ih l.1 h.2⟩; have he:= fits_separation ht.1; rw [separation_comm] at he; have hx:=budget2 (v:=v); omega
lemma prev_get (u:Spot N)(w:Spot v)(h:Prev v w (spot A u)): ∃! x:Spot N, Prev N x u∧ spot A x=w:=by
 let a:=ladder (forG N v A) u.1 w.1; have he : 2*separation a u.1 < (GridN v).val :=by
    unfold a; rw [climbs]; have he: separation ((r).cut u.1) w.1≤1:=fits_separation h.1; rw [separation_comm] at he; have hx:= budget2 (v:=v); apply lt_of_le_of_lt (Nat.mul_le_mul_left 2 he) hx
 let y: Spot N:=(a,w.2); have hp : spot A y=w:=Prod.ext (rises (forG N v A) u.1 w.1) rfl
 refine ⟨y,⟨(prev_v A y u he).2 (hp.symm ▸ h),hp⟩,fun x tX=>?_⟩; obtain ⟨a',p⟩:= tX; apply Prod.ext; · change _=a; have he:= fits_separation a'.1; rw [separation_comm] at he; unfold a; rw [← p]; exact (steps_back (forG N v A) x.1 u.1 (lt_of_le_of_lt (Nat.mul_le_mul_left 2 he) budget2)).symm
 change (spot A x).2=w.2; exact congrArg Prod.snd p
lemma move_unique (u:Spot N)(L D:List (Ramp N))(v':Moves N u L)(w:Moves N u D)(p:L.map (past A)=D.map (past A)): L=D:=by
 induction L generalizing u D with
 | nil=>simpa using p.symm
 | cons x L ih=>
   cases D with
   | nil=> simp at p
   | cons y D=>
     have hp:= List.cons.inj p; have hx:spot A x.1=spot A y.1:=congrArg Prod.fst hp.1; have he:= prev_get A u _ (show Prev v (spot A x.1) (spot A u) from (marches A u _ v').1); have ht:x=y:= Prod.ext (he.unique ⟨v'.1,rfl⟩ ⟨w.1,hx.symm⟩) (congrArg (fun z:Ramp v=>z.2) hp.1)
     subst y; rw [ih x.1 D v'.2 w.2 hp.2] -- tune
lemma frames_list (u:Spot N)(L:List (Ramp v))(h:Moves v (spot A u) L): ∃ M:List (Ramp N),Moves N u M ∧ M.map (past A)=L:=by
 induction L generalizing u with
 | nil=> exact ⟨[], trivial,rfl⟩
 | cons x L ih=> obtain ⟨y,p,τ⟩:= (prev_get A u x.1 h.1).exists; obtain ⟨Q,g,w⟩:= ih y (τ.symm ▸ h.2); refine ⟨(y,x.2)::Q,⟨p,g⟩,?_⟩; rw [List.map_cons,w]; unfold past; simp only [Prod.map_apply,id_eq]; rw [τ]
lemma range_m (p:List (Ramp N))(r':Finset Row) : InRows r' p ↔ InRows r' (p.map (past A)):=by
 constructor; · intro h q u; obtain ⟨v,q,rfl⟩:=List.mem_map.mp u; exact h v q
 exact fun h i u=> h (past A i) (List.mem_map_of_mem u)
lemma transport_r (U: Skin v B)(a b:Index N)(h:Fits N a b)(o:Lattice.Order): parcel N B ((t).links U) b a o=parcel v B U ((r).cut b) ((r).cut a) o:=by
 unfold Cube.parcel; rw [Macrame.Window.traveller, march_eq B A _ _ ?_,add_down,add_down]; exact (separation_comm _ _).trans_le (chain_near h B) -- tune
lemma carriage (U:Skin v B)(x:ArrayF v)(a: Spot N)(L:List (Ramp N))(h:Moves N a L):
 Cube.train N B ((t).links U) (x ∘ spot A) a.1 L= Cube.train v B U x ((r).cut a.1) (L.map (past A)):=by
 induction L generalizing a with
 | nil=>rfl
 | cons l L ih=>
   obtain ⟨b,i⟩:=l; rw [Cube.train,List.map_cons]; change _=((x (spot A b)).val::_).map _; rw [ih b h.2, transport_r B A U b.1 a.1 h.1.1]; rfl
lemma pays_p (U:Skin v B)(x:ArrayF v)(a: Spot N)(k:Zone) :
    fundF N B ((t).links U) (x ∘ spot A) k a=fundF v B U x k (spot A a):=by
 classical
 unfold fundF
 apply prod_bij (fun l (_:l ∈ permits N a k) => l.map (past A))
 · intro l h; obtain ⟨p,g⟩:= permits_iff.mp h; exact permits_iff.mpr ⟨marches A a l p, (range_m A l k).1 g⟩
 · intro l p v s q; exact move_unique A a l v (permits_iff.mp p).1 (permits_iff.mp s).1 q
 · intro l p; obtain ⟨v,b,z⟩:= frames_list A a l (permits_iff.mp p).1; exact ⟨v,permits_iff.mpr ⟨b,(range_m A v k).2 (z.symm ▸ (permits_iff.mp p).2)⟩,z⟩
 intro i h; unfold rateF; rw [carriage B A U x a i (permits_iff.mp h).1]; rfl
lemma chiffon (U:Skin v B)(x:Cue v)(p:ArrayF v)(r':Index N): draw N B (univ: Finset Unit) ((t).links U) (fun _=>p ∘ spot A) (fun _=>∅) 0 r' (pullS A x)= draw v B (univ:Finset Unit) U (fun _=>p) (fun _=>∅) 0 ((r).cut r') x := by
 apply prod_congr rfl; intro i _; unfold dry; rw [show capRow (p ∘ spot A) 0 (pullS A x)=capRow p 0 x ∘ spot A from ?_,pays_p B A]; · rfl
 funext ⟨i,j⟩; by_cases h:j=0 <;> simp [capRow,h,spot]
lemma same_water (U:Skin v B)(x:Cue v)(r':Index N) : water N B ((t).links U) r' (pullS A x)= water v B U ((r).cut r') x:=by
 let b:=slot v x; rw [water_base (u:=b∘spot A),water_base (x:=x) (u:=b), priceW,priceW,chiffon]; apply congrArg (fun y:ℝ=> _ / y); unfold limitW; apply integral_congr_ae; refine Filter.Eventually.of_forall fun i=>?_ ; dsimp only
 rw [←chiffon B A _ _ _ r']; apply local_draw; intro z h; let a:=(r).cut r'; by_cases p:z=r'; · subst z; unfold pullS; simp
 have he:(r).cut z≠(r).cut r':=by
    let g:= (lt_of_le_of_lt (Nat.mul_le_mul_left 2 ((separation_comm z r').trans_le (fits_separation h))) (budget2 (v:=v))); exact fun v'=> p (funext fun i=> (budget_eq (forG N v A) z r' g i).1 (congrFun v' i))
 rw [update_of_ne p]; exact (update_of_ne he i x).symm
end YM.CF.Buffered.Mail.Colony
#print axioms YM.CF.Buffered.Mail.Colony.same_water
#print axioms YM.CF.Buffered.Mail.Colony.painted
