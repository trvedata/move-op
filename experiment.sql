CREATE SEQUENCE move_ops_seq;
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";

CREATE TYPE unique_timestamp AS (
    time    timestamptz,
    counter bigint,
    id      uuid
);

CREATE TABLE move_ops2 (
    time   unique_timestamp PRIMARY KEY DEFAULT (now(), nextval('move_ops_seq'), uuid_generate_v4()),
    parent bigint  NOT NULL,
    name   text    NOT NULL,
    child  bigint  NOT NULL,
    valid  boolean NOT NULL DEFAULT 'true'
);

CREATE INDEX ON move_ops (parent);
CREATE INDEX ON move_ops (child);

CREATE OR REPLACE VIEW tree AS
SELECT m1.parent AS parent, m1.name AS name, m1.child AS child
FROM move_ops AS m1
LEFT JOIN move_ops AS m2
   ON m1.time < m2.time AND m1.child = m2.child AND m2.valid
WHERE m1.valid AND m2 IS NULL;

CREATE OR REPLACE FUNCTION ancestors_before(parent bigint, threshold unique_timestamp)
RETURNS TABLE(ancestor bigint) AS $$
  WITH RECURSIVE ancestors(ancestor) AS (
      VALUES (parent)
    UNION
      SELECT m1.parent FROM ancestors
      JOIN move_ops AS m1
         ON m1.child = ancestor AND m1.valid AND m1.time < threshold
      LEFT JOIN move_ops AS m2
         ON m2.child = ancestor AND m2.valid AND m2.time < threshold AND m1.time < m2.time
      WHERE m2 IS NULL
  )
  SELECT * from ancestors
$$ LANGUAGE SQL;

CREATE OR REPLACE FUNCTION process_move() RETURNS trigger AS $$
  DECLARE
    move RECORD;
  BEGIN
    FOR move IN SELECT * FROM move_ops WHERE time >= NEW.time ORDER BY time FOR UPDATE LOOP
      IF move.child IN (SELECT ancestors_before(move.parent, move.time)) THEN
        RAISE NOTICE 'INVALID: %', move;
        IF move.valid THEN
          UPDATE move_ops SET valid = 'false' WHERE time = move.time;
        END IF;
      ELSE
        RAISE NOTICE 'valid: %', move;
        IF NOT move.valid THEN
          UPDATE move_ops SET valid = 'true' WHERE time = move.time;
        END IF;
      END IF;
    END LOOP;
    RETURN NULL;
  END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER process_move AFTER INSERT ON move_ops
FOR EACH ROW EXECUTE FUNCTION process_move();

CREATE OR REPLACE VIEW tree_view AS
WITH RECURSIVE tree_view (node, path) AS (
    VALUES(0::bigint, ARRAY[]::text[])
  UNION ALL
    SELECT tree.child, tree_view.path || tree.name
    FROM tree_view JOIN tree ON tree_view.node = tree.parent
)
SELECT CASE
  WHEN path = array[]::text[] THEN node::text
  ELSE repeat('|- ', array_length(path, 1)) || path[array_length(path, 1)] || ': ' || node::text
  END
FROM tree_view ORDER BY path;
