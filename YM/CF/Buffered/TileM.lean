import YM.CF.Buffered.Divot
/-!
# Tile channelization + local CAR laws
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Push.SectorMeasure Ordered Cin Stripe Spire
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
structure Bays (P I:Type*) where
 site : P
 fibre : I
deriving DecidableEq
variable {P Q I J:Type*}
namespace Bays
def wall (P I:Type*) : Installed P I (Bays P I) := ⟨fun x=>⟨x.1,x.2⟩,fun x=>(x.site,x.fibre),fun _=>rfl,fun _=>rfl⟩
abbrev install (I:Type*)(p:P): I↪Bays P I:= Installed.point (wall P I) p
instance [Fintype P][Fintype I]: Fintype (Bays P I):= Fintype.ofEquiv _ (wall P I)
instance [Fintype P][Fintype I][DecidableEq P][DecidableEq I]: LinearOrder (Bays P I):= pickOrd _
end Bays
open Bays
open Installed (point)
variable {m p v w B:Side}
local notation "d" => Domain v B
local notation "N" => CSide v B
local notation "S" => Locale v B
local notation "W" => Post N
abbrev GridM (v B:Side):= Bays (Post (CSide v B)) Spin
variable {e x:ℝ}
local notation "G" => GridM v B

namespace Tile
variable (b:Ticket m v B p e x) (i j:Axis) (u: Locale v B)
local notation "Gv" z => install Spin (z: W)
def seed (b:Ticket m v B p e x)(u:S): FC G:= ∑ z:W, into (Gv z) (b.seedM z u)
def sky (v B: Side): Finset (GridM v B) := Installed.filled (wall _ _) Mil.above
def turnF (i:Axis)(v B:Side): UNI (GridM v B) := Installed.uniform (wall _ _) (mirrorR {i}) (mirrorSpin i)
lemma seat_mate (t:W) : Framed (Gv t) (Gv (shades {i} t)) (turnF i v B) (mirrorSpin i) := Installed.uniform_frame _ (mirrorR {i}) (mirrorSpin i) t
lemma turn_squared (i v B): (turnF i v B).val*(turnF i v B).val= -1:= Installed.uniform_sq _ _ _ (glass_sq i) rfl
lemma seed_sector (u:S): Sector univ false (seed b u):=by
 unfold seed; refine Sector.sumS _ _ fun i _=> ?_; apply uninstall; swap; · exact univ
 by_cases h:u∈permitted b.K e x; rw [Ticket.seedI b _ h]; apply Cin.unseed
 rw [Ticket.seedM, Set.indicator_of_notMem h]; apply Sector.zero
lemma spin_sector (k:W)(u:S): Sector univ false (b.seedM k u):=by
 by_cases h:u∈permitted b.K e x; rw [Ticket.seedI b _ h]; apply Cin.unseed
 rw [Ticket.seedM, Set.indicator_of_notMem h]; apply Sector.zero
lemma seed_refl : seed b (Rails.past {i} u)=theta (turnF i v B) (seed b u):= by
 unfold seed; rw [theta_sum,←Equiv.sum_comp (mirrorR {i}) (fun z:W=> theta (turnF i v B) (into (Gv z) (b.seedM z u)))]; refine sum_congr rfl fun v _=>?_ ; rw [Ticket.seed_turn b, (seat_mate i _).theta _ (spin_sector b _ _), show mirrorR {i} v=shades {i} v from rfl,shades_square]
lemma seed_paid : Envelope (seed b):= Env.total univ (fun i=> Girt.pole_w _ _ (into_cont _) (b.seed_pays i))

def innerEdge (x:Minor N i)(u:S): FC G:= Mil.coupled (Gv x.val) (Gv (reach i x)) i (outWay i x.val u* inWay i (reach i x) u)
def pit (u:S): FC G := (∑ x:W, into (Gv x) rest)+ ∑ i:Axis,∑ x:Minor N i, innerEdge i x u
lemma rest_placed : Sector univ false rest:= undg _
lemma pit_turn : pit (Rails.past {i} u) = theta (turnF i v B) (pit u):=by
 let A:= turnF i v B
 unfold pit; rw [theta_add]; apply congrArg₂ (· + ·)
 · rw [theta_sum, ←Equiv.sum_comp (mirrorR {i}) (fun j:W=> into (Gv j) rest)]; apply sum_congr rfl; intro v _; rw [(seat_mate i _).theta _ rest_placed, rest_turn]; rfl
 rw [theta_sum]; refine sum_congr rfl fun s _=> ?_; rw [theta_sum]; by_cases h:s=i
 · subst s; rw [←Equiv.sum_comp (flipAlong i) (fun (y:Minor N i)=> innerEdge i y (Rails.past {i} u))]; apply sum_congr rfl; intro v' _
   unfold innerEdge
   rw [Mil.edge_turn i _ _ (seat_mate i _) (seat_mate i _) (Installed.apart (wall W Spin) (fun eq=>reach_lt i v' ((mirrorR {i}).injective eq).symm)) _,way_x,way_i,mul_inv_rev,show (flipAlong i v')= alongTail i v' from rfl,show (alongTail i v').val=shades {i} (reach i v') from rfl, sendAlong,shades_square,shades_square]
 rw [←Equiv.sum_comp (acrossMinor s i h) (fun (v':Minor N s)=> innerEdge s v' (Rails.past {i} u))]; apply sum_congr rfl; intro t _
 unfold innerEdge; rw [Mil.transverse i s _ _ (seat_mate i _) (seat_mate i _) (Installed.apart (wall W Spin) (fun eq=> reach_lt s t ((mirrorR {i}).injective eq).symm)) _ (Ne.symm h),way_t s i _ _ h,way_o s i _ _ h,show reach s (acrossMinor s i h t)=shades {i} (reach s t) from Subtype.ext (shades_reach s i t h).symm, show (acrossMinor s i h t).val=shades {i} t.val from rfl,shades_square,shades_square]
lemma pit_cont : Continuous (pit (v:=v) (B:=B)) := continuous_const.add (continuous_finsetSum _ fun i _=>continuous_finsetSum _ fun j _=> (Mil.coupled_cont ..).comp ((way_cont i j.val).2.mul (way_cont i (reach i j)).1))
lemma pit_sector (u:S): Sector univ false (pit u):= by unfold pit; exact (Sector.sumS _ _ (fun i _=>uninstall _ rest_placed)).add (Sector.sumS _ _ (fun i _=>Sector.sumS _ _ (fun j _=> coupled_sector ..)))

abbrev Kid (v B:Side)(i:Axis) := Hale (CSide v B) i × Mouth
def outgo (i:Axis)(j:Kid v B i)(u:S) := into (Gv j.1.val) (outlet i (outWay i j.1.val u) j.2)
def income (i:Axis)(j:Kid v B i)(u:S) := into (Gv (pulse i j.1)) (inlet i (inWay i (pulse i j.1) u) j.2)
lemma outs_sector (j:Kid v B i) (u:S):Sector univ true (outgo i j u):= uninstall _ (outlet_sector ..)
lemma ins_sector (j:Kid v B i) (u:S):Sector univ true (income i j u):= uninstall _ (inlet_sector ..)
lemma leg_swap (j k:Kid v B i)(u:S): income i j u*outgo i k u= -(outgo i k u*income i j u):=by
 have he : pulse i j.1≠k.1.val:=by intro e; have hz:= pulse_val i j.1; rw [e,show k.1.val.val i=(CSide v B).val-1 from k.1.property] at hz; have ht:=suff_pos v B; omega
 unfold income outgo; simpa only [Sector.grainB,Bool.and_true,ite_true,neg_smul,one_smul] using Sector.apart (sector_in (Gv (pulse i j.1)) (inlet_sector i (inWay i (pulse i j.1) u) j.2)) (sector_in (Gv k.1.val) (outlet_sector i (outWay i k.1.val u) k.2)) (Installed.apart (wall W Spin) he)
lemma legs_cont (j:Kid v B i): Continuous (outgo i j) ∧ Continuous (income i j):=⟨(into_cont _).comp ((outlet_cont ..).comp (way_cont i j.1.val).2),(into_cont _).comp ((inlet_cont ..).comp (way_cont i _).1)⟩
lemma outlook (j:Kid v B i) : outgo i j (Rails.past {i} u)=theta (turnF i v B) (income i j u):=by
 unfold income outgo; rw [(seat_mate i _).theta _ (inlet_sector ..),way_x]; unfold pulse outlet; rw [shades_square,inv_inv]
lemma inch (j:Kid v B i) : income i j (Rails.past {i} u)=theta (turnF i v B) (outgo i j u):=by
 unfold income outgo; rw [(seat_mate i _).theta _ (outlet_sector ..),way_i,outlet_turn]; unfold pulse; rw [shades_square]

section bond
variable [LinearOrder I][Fintype I][LinearOrder J][Fintype J]
variable (f g: GridM v B↪I)(z:Locale v B)
def joinF (s:S × S): FC I := ∑ j: Hale N i, Mil.coupled ((Gv j.val).trans f) ((Gv (pulse i j)).trans g) i (outWay i j.val s.1*inWay i (pulse i j) s.2)
lemma join_cont : Continuous (joinF i f g):= continuous_finsetSum _ fun j _=> (Mil.coupled_cont ..).comp (((way_cont i _).2.comp continuous_fst).mul ((way_cont i _).1.comp continuous_snd))
lemma join_local : Sector univ false (joinF i f g (u,z)):= by unfold joinF; exact Sector.sumS _ _ fun _ _=> Mil.coupled_sector ..
lemma seated_sub (f:G↪I)(t:W): lows ((Gv t).trans f) ⊆ lows f:=by intro z h; obtain ⟨x,_,rfl⟩:= mem_map.mp h; exact coil_hit ..
lemma join_across (h: Disjoint (lows f) (lows g)) :
 joinF i f g (u,z)= ∑ j:Kid v B i, Complex.I • (into f (outgo i j u) * into g (income i j z)):=by
 unfold joinF
 -- use all both ports choices, local reflection frame. no wrap cost here.
 conv_rhs=> rw [Fintype.sum_prod_type]
 apply sum_congr rfl; intro v _
 rw [bond_value i _ _ _ _ (Disjoint.mono (seated_sub f v.val) (seated_sub g (pulse i v)) h)]
 refine sum_congr rfl fun j _=>?_ ; unfold outgo income; rw [into_trans _ ((install Spin v.val).trans f) f (fun _=>rfl) (outlet_sector ..),into_trans _ ((install Spin (pulse i v)).trans g) g (fun _=>rfl) (inlet_sector ..)] -- tune
lemma join_turn {U:UNI I}(t:Framed f f U (turnF j v B))(k:Framed g g U (turnF j v B))(h: Disjoint (lows f) (lows g))(p:i≠j): joinF i f g (Rails.past {j} u,Rails.past {j} z)=theta U (joinF i f g (u,z)):=by
 unfold joinF; rw [theta_sum,←Equiv.sum_comp (acrossHale i j p) (fun x:Hale N i=> Mil.coupled ((Gv x.val).trans f) ((Gv (pulse i x)).trans g) i (outWay i x.val (Rails.past {j} u)*inWay i (pulse i x) (Rails.past {j} z)))]; apply sum_congr rfl; intro a _
 rw [Mil.transverse j i _ _ ((seat_mate j a.val).trans _ t) ((seat_mate j (pulse i a)).trans _ k) (Disjoint.mono (seated_sub f _) (seated_sub g _) h) _ (Ne.symm p)]; simp only; rw [way_t i j _ u p, way_o i j _ z p]; rw [show (acrossHale i j p a).val=shades {j} a.val from rfl]; unfold pulse; rw [show (acrossHale i j p a).val=shades {j} a.val from rfl,Waist i j,shades_square,shades_square] -- tune
lemma join_through (t:I↪J)(F G':GridM v B↪J)(h:∀ i, t (f i)=F i)(p:∀ i,t (g i)=G' i): into t (joinF i f g (u,z))= joinF i F G' (u,z):=by unfold joinF; rw [map_sum]; exact sum_congr rfl fun j _=> coupled_into i _ _ _ _ _ (fun i=>h _) (fun i=>p _) _
end bond
end Tile
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Tile.join_across
#print axioms YM.CF.Buffered.Region.Tile.pit_turn
